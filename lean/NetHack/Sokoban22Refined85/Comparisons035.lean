/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4900 (p : Pattern) (guard : d0 p = 1) : d217 p ≤ (2 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4901 (p : Pattern) (guard : d4299 p = 1) : d218 p ≤ (2 : Int) + d213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d4299, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d4299, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4902 (p : Pattern) (guard : d4432 p = 1) : d219 p ≤ (2 : Int) + d213 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4892 p hg
    simpa only [d4432, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4901 p hg
    simpa only [d4432, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4903 (p : Pattern) (guard : d4432 p = 1) : d220 p ≤ (2 : Int) + d4451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d220, d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4793 p hg
    simpa only [d220, d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d220, d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d220, d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4904 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4905 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4906 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4907 (p : Pattern) (guard : d4299 p = 1) : d155 p ≤ (2 : Int) + d213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4905 p hg
    simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4908 (p : Pattern) (guard : d4432 p = 1) : d221 p ≤ (2 : Int) + d213 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4892 p hg
    simpa only [d4432, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4907 p hg
    simpa only [d4432, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4909 (p : Pattern) (guard : d4432 p = 1) : d222 p ≤ (2 : Int) + d4451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d222, d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4813 p hg
    simpa only [d222, d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d222, d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4908 p hg
    simpa only [d222, d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4910 (p : Pattern) (guard : d4432 p = 1) : d223 p ≤ (2 : Int) + d4451 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4903 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4909 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4911 (p : Pattern) (guard : d4432 p = 1) : d224 p ≤ (2 : Int) + d4452 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d224, d4452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4909 p hg
    simpa only [d224, d4452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d224, d4452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4823 p hg
    simpa only [d224, d4452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4912 (p : Pattern) (guard : d4432 p = 1) : d225 p ≤ (2 : Int) + d4453 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d225, d4453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4910 p hg
    simpa only [d225, d4453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d225, d4453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4911 p hg
    simpa only [d225, d4453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4913 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d5 p := by
  change (3 : Int) ≤ (2 : Int) + 5
  decide
theorem compare4914 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4915 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4914 p hg
    simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4916 (p : Pattern) (guard : d1 p = 1) : d226 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d226, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d226, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d226, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d226, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4917 (p : Pattern) (guard : d1 p = 1) : d227 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d227, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d227, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d227, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4916 p hg
    simpa only [d227, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4918 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d10 p := by
  change (5 : Int) ≤ (2 : Int) + 10
  decide
theorem compare4919 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4918 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4920 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4918 p hg
    simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4919 p hg
    simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4921 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4920 p hg
    simpa only [d125, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d125, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4922 (p : Pattern) (guard : d1 p = 1) : d215 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d215, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4921 p hg
    simpa only [d215, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d215, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d215, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4923 (p : Pattern) (guard : d1 p = 1) : d228 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d228, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4917 p hg
    simpa only [d228, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d228, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d228, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4924 (p : Pattern) (guard : d0 p = 1) : d231 p ≤ (2 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4925 (p : Pattern) (guard : d4299 p = 1) : d232 p ≤ (2 : Int) + d113 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4923 p hg
    simpa only [d4299, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4924 p hg
    simpa only [d4299, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4926 (p : Pattern) (guard : d4432 p = 1) : d233 p ≤ (2 : Int) + d113 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d4432, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4925 p hg
    simpa only [d4432, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4927 (p : Pattern) (guard : d1 p = 1) : d234 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d234, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d234, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d234, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d234, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4928 (p : Pattern) (guard : d1 p = 1) : d235 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d235, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d235, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d235, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d235, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4929 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d12 p := by
  change (7 : Int) ≤ (2 : Int) + 12
  decide
theorem compare4930 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4931 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4932 (p : Pattern) (guard : d1 p = 1) : d229 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4933 (p : Pattern) (guard : d1 p = 1) : d230 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4932 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4934 (p : Pattern) (guard : d1 p = 1) : d236 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d236, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4928 p hg
    simpa only [d236, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d236, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4933 p hg
    simpa only [d236, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4935 (p : Pattern) (guard : d0 p = 1) : d237 p ≤ (2 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4936 (p : Pattern) (guard : d4299 p = 1) : d238 p ≤ (2 : Int) + d213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4934 p hg
    simpa only [d4299, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4935 p hg
    simpa only [d4299, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4937 (p : Pattern) (guard : d4432 p = 1) : d239 p ≤ (2 : Int) + d213 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4892 p hg
    simpa only [d4432, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d4432, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4938 (p : Pattern) (guard : d4432 p = 1) : d240 p ≤ (2 : Int) + d4451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d240, d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4926 p hg
    simpa only [d240, d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d240, d4451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4937 p hg
    simpa only [d240, d4451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4939 (p : Pattern) (guard : d0 p = 1) : d243 p ≤ (2 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4940 (p : Pattern) (guard : d4432 p = 1) : d244 p ≤ (2 : Int) + d137 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4939 p hg
    simpa only [d4432, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d4432, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4941 (p : Pattern) (guard : d0 p = 1) : d246 p ≤ (2 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4942 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d7 p := by
  change (9 : Int) ≤ (2 : Int) + 7
  decide
theorem compare4943 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d23, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4944 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d24, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d24, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4945 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (2 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4944 p hg
    simpa only [d25, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d25, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4946 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (2 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4944 p hg
    simpa only [d26, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4945 p hg
    simpa only [d26, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4947 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (2 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4946 p hg
    simpa only [d27, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d27, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4948 (p : Pattern) (guard : d1 p = 1) : d247 p ≤ (2 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d247, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4947 p hg
    simpa only [d247, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d247, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d247, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4949 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4950 (p : Pattern) (guard : d4299 p = 1) : d248 p ≤ (2 : Int) + d154 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4948 p hg
    simpa only [d4299, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4949 p hg
    simpa only [d4299, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4951 (p : Pattern) (guard : d4432 p = 1) : d249 p ≤ (2 : Int) + d154 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4941 p hg
    simpa only [d4432, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4950 p hg
    simpa only [d4432, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4952 (p : Pattern) (guard : d4432 p = 1) : d250 p ≤ (2 : Int) + d4454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d250, d4454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4940 p hg
    simpa only [d250, d4454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d250, d4454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4951 p hg
    simpa only [d250, d4454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4953 (p : Pattern) (guard : d4432 p = 1) : d251 p ≤ (2 : Int) + d4455 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d251, d4455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4938 p hg
    simpa only [d251, d4455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d251, d4455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4952 p hg
    simpa only [d251, d4455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4954 (p : Pattern) (guard : d0 p = 1) : d256 p ≤ (2 : Int) + d255 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4955 (p : Pattern) (guard : d1 p = 1) : d257 p ≤ (2 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d257, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d257, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d257, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d257, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4956 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (2 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d258, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4955 p hg
    simpa only [d258, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d258, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d258, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4957 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d255 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4958 (p : Pattern) (guard : d4299 p = 1) : d259 p ≤ (2 : Int) + d255 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d4299, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4957 p hg
    simpa only [d4299, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4959 (p : Pattern) (guard : d4432 p = 1) : d260 p ≤ (2 : Int) + d255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d4432, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4958 p hg
    simpa only [d4432, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4960 (p : Pattern) (guard : d4432 p = 1) : d261 p ≤ (2 : Int) + d4456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d261, d4456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d261, d4456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d261, d4456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4951 p hg
    simpa only [d261, d4456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4961 (p : Pattern) (guard : d4432 p = 1) : d262 p ≤ (2 : Int) + d4457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d262, d4457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4960 p hg
    simpa only [d262, d4457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d262, d4457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d262, d4457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4962 (p : Pattern) (guard : d4432 p = 1) : d263 p ≤ (2 : Int) + d4458 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d263, d4458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4953 p hg
    simpa only [d263, d4458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d263, d4458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4961 p hg
    simpa only [d263, d4458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4963 (p : Pattern) (guard : d4432 p = 1) : d264 p ≤ (2 : Int) + d4459 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d264, d4459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4912 p hg
    simpa only [d264, d4459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d264, d4459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4962 p hg
    simpa only [d264, d4459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4964 (p : Pattern) (guard : d4432 p = 1) : d265 p ≤ (2 : Int) + d4460 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d265, d4460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d265, d4460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d265, d4460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4963 p hg
    simpa only [d265, d4460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4965 (p : Pattern) (guard : d4432 p = 1) : d266 p ≤ (2 : Int) + d4461 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d266, d4461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4891 p hg
    simpa only [d266, d4461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d266, d4461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4964 p hg
    simpa only [d266, d4461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4966 (p : Pattern) (guard : d4432 p = 1) : d267 p ≤ (2 : Int) + d4462 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d267, d4462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4830 p hg
    simpa only [d267, d4462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d267, d4462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d267, d4462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4967 (p : Pattern) (guard : d4203 p = 1) : d88 p ≤ (0 : Int) + d517 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1897 p hg
    simpa only [d4203, d88, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4968 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4969 (p : Pattern) (guard : d4117 p = 1) : d82 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d82, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d82, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d82, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4968 p hg
    simpa only [d4117, d82, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4970 (p : Pattern) (guard : d0 p = 1) : d85 p ≤ (0 : Int) + d541 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4971 (p : Pattern) (guard : d4117 p = 1) : d86 p ≤ (0 : Int) + d542 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d86, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d86, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d86, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d4117, d86, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4972 (p : Pattern) (guard : d4117 p = 1) : d87 p ≤ (0 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d87, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d87, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d87, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4971 p hg
    simpa only [d87, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4973 (p : Pattern) (guard : d0 p = 1) : d96 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4974 (p : Pattern) (guard : d4203 p = 1) : d97 p ≤ (0 : Int) + d544 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d97, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d4203, d97, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d97, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4973 p hg
    simpa only [d4203, d97, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4975 (p : Pattern) (guard : d4203 p = 1) : d98 p ≤ (0 : Int) + d545 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4967 p hg
    simpa only [d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4974 p hg
    simpa only [d98, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4976 (p : Pattern) (guard : d4203 p = 1) : d88 p ≤ (0 : Int) + d546 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1960 p hg
    simpa only [d4203, d88, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4977 (p : Pattern) (guard : d4203 p = 1) : d99 p ≤ (0 : Int) + d547 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d99, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d4203, d99, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d99, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d99, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4978 (p : Pattern) (guard : d4203 p = 1) : d100 p ≤ (0 : Int) + d548 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d100, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4976 p hg
    simpa only [d100, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d100, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d100, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4979 (p : Pattern) (guard : d4203 p = 1) : d101 p ≤ (0 : Int) + d549 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d101, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d101, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d101, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4978 p hg
    simpa only [d101, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4980 (p : Pattern) (guard : d4203 p = 1) : d88 p ≤ (0 : Int) + d550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1903 p hg
    simpa only [d4203, d88, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4981 (p : Pattern) (guard : d0 p = 1) : d96 p ≤ (0 : Int) + d441 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4982 (p : Pattern) (guard : d4203 p = 1) : d97 p ≤ (0 : Int) + d551 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d97, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d4203, d97, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d97, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4981 p hg
    simpa only [d4203, d97, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4983 (p : Pattern) (guard : d4203 p = 1) : d98 p ≤ (0 : Int) + d552 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4982 p hg
    simpa only [d98, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4984 (p : Pattern) (guard : d4203 p = 1) : d88 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d4203, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1967 p hg
    simpa only [d4203, d88, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4985 (p : Pattern) (guard : d4203 p = 1) : d100 p ≤ (0 : Int) + d554 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d100, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4984 p hg
    simpa only [d100, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d100, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d100, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4986 (p : Pattern) (guard : d4203 p = 1) : d101 p ≤ (0 : Int) + d555 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d101, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d101, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d101, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4985 p hg
    simpa only [d101, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4987 (p : Pattern) (guard : d4203 p = 1) : d101 p ≤ (0 : Int) + d556 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4979 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4988 (p : Pattern) (guard : d4203 p = 1) : d158 p ≤ (0 : Int) + d557 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d4203, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1911 p hg
    simpa only [d4203, d158, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4989 (p : Pattern) (guard : d0 p = 1) : d151 p ≤ (0 : Int) + d568 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4990 (p : Pattern) (guard : d4117 p = 1) : d152 p ≤ (0 : Int) + d569 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d152, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d152, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d152, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4989 p hg
    simpa only [d4117, d152, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4991 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4992 (p : Pattern) (guard : d4117 p = 1) : d156 p ≤ (0 : Int) + d578 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d156, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d156, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d156, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4991 p hg
    simpa only [d4117, d156, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4993 (p : Pattern) (guard : d4117 p = 1) : d157 p ≤ (0 : Int) + d579 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d157, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d157, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d157, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d157, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4994 (p : Pattern) (guard : d0 p = 1) : d162 p ≤ (0 : Int) + d441 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4995 (p : Pattern) (guard : d4203 p = 1) : d163 p ≤ (0 : Int) + d580 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d163, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d4203, d163, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d163, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d4203, d163, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4996 (p : Pattern) (guard : d4203 p = 1) : d164 p ≤ (0 : Int) + d581 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4995 p hg
    simpa only [d164, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4997 (p : Pattern) (guard : d4203 p = 1) : d158 p ≤ (0 : Int) + d582 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d4203, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1975 p hg
    simpa only [d4203, d158, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4998 (p : Pattern) (guard : d4203 p = 1) : d165 p ≤ (0 : Int) + d583 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d165, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d4203, d165, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d165, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d165, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4999 (p : Pattern) (guard : d4203 p = 1) : d166 p ≤ (0 : Int) + d584 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d166, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4997 p hg
    simpa only [d166, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d166, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d166, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5000 (p : Pattern) (guard : d4203 p = 1) : d167 p ≤ (0 : Int) + d585 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d167, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4996 p hg
    simpa only [d167, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d167, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4999 p hg
    simpa only [d167, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5001 (p : Pattern) (guard : d4203 p = 1) : d168 p ≤ (0 : Int) + d586 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d168, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4979 p hg
    simpa only [d168, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d168, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5000 p hg
    simpa only [d168, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5002 (p : Pattern) (guard : d4203 p = 1) : d169 p ≤ (0 : Int) + d587 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d169, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4987 p hg
    simpa only [d169, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d169, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5001 p hg
    simpa only [d169, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5003 (p : Pattern) (guard : d0 p = 1) : d178 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5004 (p : Pattern) (guard : d4117 p = 1) : d179 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d179, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d179, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d179, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5003 p hg
    simpa only [d4117, d179, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5005 (p : Pattern) (guard : d0 p = 1) : d185 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5006 (p : Pattern) (guard : d4117 p = 1) : d186 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d186, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d186, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d186, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5005 p hg
    simpa only [d4117, d186, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5007 (p : Pattern) (guard : d4117 p = 1) : d187 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d187, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5004 p hg
    simpa only [d187, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d187, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5006 p hg
    simpa only [d187, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5008 (p : Pattern) (guard : d0 p = 1) : d205 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5009 (p : Pattern) (guard : d4203 p = 1) : d206 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d206, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5007 p hg
    simpa only [d4203, d206, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d206, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5008 p hg
    simpa only [d4203, d206, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5010 (p : Pattern) (guard : d0 p = 1) : d196 p ≤ (0 : Int) + d595 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5011 (p : Pattern) (guard : d4117 p = 1) : d197 p ≤ (0 : Int) + d596 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d197, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d4117, d197, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d197, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5010 p hg
    simpa only [d4117, d197, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5012 (p : Pattern) (guard : d0 p = 1) : d203 p ≤ (0 : Int) + d603 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5013 (p : Pattern) (guard : d4117 p = 1) : d204 p ≤ (0 : Int) + d604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d204, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d4117, d204, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d204, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5012 p hg
    simpa only [d4117, d204, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5014 (p : Pattern) (guard : d4117 p = 1) : d205 p ≤ (0 : Int) + d605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d205, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5011 p hg
    simpa only [d205, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d205, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5013 p hg
    simpa only [d205, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5015 (p : Pattern) (guard : d4203 p = 1) : d207 p ≤ (0 : Int) + d606 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d207, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d4203, d207, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d207, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d207, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5016 (p : Pattern) (guard : d4203 p = 1) : d208 p ≤ (0 : Int) + d607 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d208, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5009 p hg
    simpa only [d208, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d208, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5015 p hg
    simpa only [d208, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5017 (p : Pattern) (guard : d4203 p = 1) : d209 p ≤ (0 : Int) + d608 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d209, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d209, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d209, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d209, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5018 (p : Pattern) (guard : d4203 p = 1) : d210 p ≤ (0 : Int) + d609 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d210, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4979 p hg
    simpa only [d210, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d210, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5017 p hg
    simpa only [d210, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5019 (p : Pattern) (guard : d4203 p = 1) : d223 p ≤ (0 : Int) + d610 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3419 p hg
    simpa only [d4203, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1923 p hg
    simpa only [d4203, d223, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5020 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d614 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5021 (p : Pattern) (guard : d4117 p = 1) : d221 p ≤ (0 : Int) + d615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d221, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d221, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d221, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5020 p hg
    simpa only [d4117, d221, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5022 (p : Pattern) (guard : d4117 p = 1) : d222 p ≤ (0 : Int) + d616 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d222, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d222, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d222, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5021 p hg
    simpa only [d222, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5023 (p : Pattern) (guard : d4203 p = 1) : d224 p ≤ (0 : Int) + d617 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d224, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5022 p hg
    simpa only [d4203, d224, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d224, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d4203, d224, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5024 (p : Pattern) (guard : d4203 p = 1) : d225 p ≤ (0 : Int) + d618 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5019 p hg
    simpa only [d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5023 p hg
    simpa only [d225, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5025 (p : Pattern) (guard : d0 p = 1) : d232 p ≤ (0 : Int) + d280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5026 (p : Pattern) (guard : d4117 p = 1) : d233 p ≤ (0 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d233, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d233, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d233, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5025 p hg
    simpa only [d4117, d233, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5027 (p : Pattern) (guard : d0 p = 1) : d238 p ≤ (0 : Int) + d288 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5028 (p : Pattern) (guard : d4117 p = 1) : d239 p ≤ (0 : Int) + d289 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d239, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d239, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d239, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5027 p hg
    simpa only [d4117, d239, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5029 (p : Pattern) (guard : d4117 p = 1) : d240 p ≤ (0 : Int) + d290 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d240, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5026 p hg
    simpa only [d240, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d240, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5028 p hg
    simpa only [d240, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5030 (p : Pattern) (guard : d0 p = 1) : d250 p ≤ (0 : Int) + d473 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5031 (p : Pattern) (guard : d4203 p = 1) : d251 p ≤ (0 : Int) + d619 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d251, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5029 p hg
    simpa only [d4203, d251, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d251, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5030 p hg
    simpa only [d4203, d251, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5032 (p : Pattern) (guard : d0 p = 1) : d259 p ≤ (0 : Int) + d630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5033 (p : Pattern) (guard : d4117 p = 1) : d260 p ≤ (0 : Int) + d631 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d260, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d4117, d260, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d260, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5032 p hg
    simpa only [d4117, d260, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5034 (p : Pattern) (guard : d0 p = 1) : d248 p ≤ (0 : Int) + d644 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5035 (p : Pattern) (guard : d4117 p = 1) : d249 p ≤ (0 : Int) + d645 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d249, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d4117, d249, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d249, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5034 p hg
    simpa only [d4117, d249, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5036 (p : Pattern) (guard : d4117 p = 1) : d261 p ≤ (0 : Int) + d646 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d261, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5033 p hg
    simpa only [d261, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d261, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5035 p hg
    simpa only [d261, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5037 (p : Pattern) (guard : d4203 p = 1) : d262 p ≤ (0 : Int) + d647 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d262, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5036 p hg
    simpa only [d4203, d262, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d262, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d262, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5038 (p : Pattern) (guard : d4203 p = 1) : d263 p ≤ (0 : Int) + d648 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d263, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5031 p hg
    simpa only [d263, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d263, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5037 p hg
    simpa only [d263, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5039 (p : Pattern) (guard : d4203 p = 1) : d264 p ≤ (0 : Int) + d649 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d264, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5024 p hg
    simpa only [d264, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d264, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5038 p hg
    simpa only [d264, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
