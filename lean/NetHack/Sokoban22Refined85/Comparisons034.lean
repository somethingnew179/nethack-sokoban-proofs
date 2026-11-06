/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4760 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (2 : Int) + d91 p := by
  omega
theorem compare4761 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d91 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4762 (p : Pattern) (guard : d4299 p = 1) : d93 p ≤ (2 : Int) + d91 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4760 p hg
    simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4761 p hg
    simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4763 (p : Pattern) (guard : d4432 p = 1) : d94 p ≤ (2 : Int) + d91 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4759 p hg
    simpa only [d4432, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d4432, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4764 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4765 (p : Pattern) (guard : d4299 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare4766 (p : Pattern) (guard : d4432 p = 1) : d95 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4764 p hg
    simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4765 p hg
    simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4767 (p : Pattern) (guard : d4432 p = 1) : d96 p ≤ (2 : Int) + d4434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d96, d4434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4763 p hg
    simpa only [d96, d4434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d96, d4434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4766 p hg
    simpa only [d96, d4434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4768 (p : Pattern) (guard : d4432 p = 1) : d97 p ≤ (2 : Int) + d4435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d97, d4435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d97, d4435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d97, d4435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4767 p hg
    simpa only [d97, d4435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4769 (p : Pattern) (guard : d4432 p = 1) : d98 p ≤ (2 : Int) + d4436 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d98, d4436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4758 p hg
    simpa only [d98, d4436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d98, d4436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4768 p hg
    simpa only [d98, d4436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4770 (p : Pattern) (guard : d4432 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare4771 (p : Pattern) (guard : d4432 p = 1) : d99 p ≤ (2 : Int) + d4437 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d99, d4437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d99, d4437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d99, d4437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d99, d4437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4772 (p : Pattern) (guard : d4432 p = 1) : d100 p ≤ (2 : Int) + d4438 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d100, d4438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4758 p hg
    simpa only [d100, d4438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d100, d4438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4771 p hg
    simpa only [d100, d4438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4773 (p : Pattern) (guard : d4432 p = 1) : d101 p ≤ (2 : Int) + d4439 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d101, d4439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d101, d4439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d101, d4439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4772 p hg
    simpa only [d101, d4439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4774 (p : Pattern) (guard : d0 p = 1) : d114 p ≤ (2 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4775 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2200 p hg
    simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4776 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d5 p := by
  change (1 : Int) ≤ (2 : Int) + 5
  decide
theorem compare4777 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4778 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4777 p hg
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4779 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4778 p hg
    simpa only [d122, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d122, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4780 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4775 p hg
    simpa only [d123, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d123, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4781 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d10 p := by
  change (1 : Int) ≤ (2 : Int) + 10
  decide
theorem compare4782 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4781 p hg
    simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4783 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4781 p hg
    simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d103, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4784 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4783 p hg
    simpa only [d124, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d124, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4785 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d12 p := by
  change (5 : Int) ≤ (2 : Int) + 12
  decide
theorem compare4786 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4787 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4788 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4789 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4784 p hg
    simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d126, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4790 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4780 p hg
    simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4789 p hg
    simpa only [d127, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4791 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (2 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4792 (p : Pattern) (guard : d4299 p = 1) : d130 p ≤ (2 : Int) + d113 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4790 p hg
    simpa only [d4299, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4791 p hg
    simpa only [d4299, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4793 (p : Pattern) (guard : d4432 p = 1) : d131 p ≤ (2 : Int) + d113 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d4432, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4792 p hg
    simpa only [d4432, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4794 (p : Pattern) (guard : d0 p = 1) : d138 p ≤ (2 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4795 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d11 p := by
  change (3 : Int) ≤ (2 : Int) + 11
  decide
theorem compare4796 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4795 p hg
    simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d115, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4797 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4795 p hg
    simpa only [d116, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4796 p hg
    simpa only [d116, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4798 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4797 p hg
    simpa only [d139, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d139, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4799 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (2 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d140, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4798 p hg
    simpa only [d140, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4800 (p : Pattern) (guard : d1 p = 1) : d141 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1840 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4801 (p : Pattern) (guard : d1 p = 1) : d142 p ≤ (2 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d142, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4799 p hg
    simpa only [d142, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d142, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d142, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4802 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (2 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4803 (p : Pattern) (guard : d4299 p = 1) : d145 p ≤ (2 : Int) + d137 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d4299, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4802 p hg
    simpa only [d4299, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4804 (p : Pattern) (guard : d4432 p = 1) : d146 p ≤ (2 : Int) + d137 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4794 p hg
    simpa only [d4432, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4803 p hg
    simpa only [d4432, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4805 (p : Pattern) (guard : d4432 p = 1) : d147 p ≤ (2 : Int) + d4440 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d147, d4440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4793 p hg
    simpa only [d147, d4440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d147, d4440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d147, d4440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4806 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2200 p hg
    simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4807 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4808 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d149, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d149, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4809 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4810 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4808 p hg
    simpa only [d150, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d150, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4811 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4812 (p : Pattern) (guard : d4299 p = 1) : d151 p ≤ (2 : Int) + d113 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4810 p hg
    simpa only [d4299, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d4299, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4813 (p : Pattern) (guard : d4432 p = 1) : d152 p ≤ (2 : Int) + d113 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d4432, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4812 p hg
    simpa only [d4432, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4814 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (2 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d153, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d153, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4815 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (2 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d154, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d154, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4816 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4817 (p : Pattern) (guard : d4299 p = 1) : d155 p ≤ (2 : Int) + d137 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4815 p hg
    simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d4299, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4818 (p : Pattern) (guard : d4432 p = 1) : d156 p ≤ (2 : Int) + d137 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4794 p hg
    simpa only [d4432, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d4432, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4819 (p : Pattern) (guard : d4432 p = 1) : d157 p ≤ (2 : Int) + d4440 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d157, d4440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4813 p hg
    simpa only [d157, d4440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d157, d4440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4818 p hg
    simpa only [d157, d4440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4820 (p : Pattern) (guard : d4432 p = 1) : d158 p ≤ (2 : Int) + d4440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4805 p hg
    simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4821 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4822 (p : Pattern) (guard : d4432 p = 1) : d161 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4821 p hg
    simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4765 p hg
    simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4823 (p : Pattern) (guard : d4432 p = 1) : d162 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4822 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4824 (p : Pattern) (guard : d4432 p = 1) : d163 p ≤ (2 : Int) + d4441 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d163, d4441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d163, d4441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d163, d4441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4823 p hg
    simpa only [d163, d4441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4825 (p : Pattern) (guard : d4432 p = 1) : d164 p ≤ (2 : Int) + d4442 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d164, d4442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4820 p hg
    simpa only [d164, d4442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d164, d4442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4824 p hg
    simpa only [d164, d4442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4826 (p : Pattern) (guard : d4432 p = 1) : d165 p ≤ (2 : Int) + d4441 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d165, d4441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d165, d4441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d165, d4441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d165, d4441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4827 (p : Pattern) (guard : d4432 p = 1) : d166 p ≤ (2 : Int) + d4442 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d166, d4442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4820 p hg
    simpa only [d166, d4442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d166, d4442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4826 p hg
    simpa only [d166, d4442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4828 (p : Pattern) (guard : d4432 p = 1) : d167 p ≤ (2 : Int) + d4442 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4825 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4827 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4829 (p : Pattern) (guard : d4432 p = 1) : d168 p ≤ (2 : Int) + d4443 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d168, d4443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d168, d4443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d168, d4443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4828 p hg
    simpa only [d168, d4443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4830 (p : Pattern) (guard : d4432 p = 1) : d169 p ≤ (2 : Int) + d4444 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d169, d4444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d169, d4444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d169, d4444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d169, d4444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4831 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d4 p := by
  change (2 : Int) ≤ (2 : Int) + 4
  decide
theorem compare4832 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4833 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4834 (p : Pattern) (guard : d1 p = 1) : d170 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d170, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d170, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d170, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d170, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4835 (p : Pattern) (guard : d1 p = 1) : d171 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d171, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d171, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d171, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4834 p hg
    simpa only [d171, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4836 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d9 p := by
  change (2 : Int) ≤ (2 : Int) + 9
  decide
theorem compare4837 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4836 p hg
    simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4838 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4836 p hg
    simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4837 p hg
    simpa only [d31, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4839 (p : Pattern) (guard : d1 p = 1) : d172 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4838 p hg
    simpa only [d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d172, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4840 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d12 p := by
  change (6 : Int) ≤ (2 : Int) + 12
  decide
theorem compare4841 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4842 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4843 (p : Pattern) (guard : d1 p = 1) : d173 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4842 p hg
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4844 (p : Pattern) (guard : d1 p = 1) : d174 p ≤ (2 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d174, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4839 p hg
    simpa only [d174, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d174, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4843 p hg
    simpa only [d174, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4845 (p : Pattern) (guard : d1 p = 1) : d175 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d175, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4835 p hg
    simpa only [d175, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d175, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4844 p hg
    simpa only [d175, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4846 (p : Pattern) (guard : d0 p = 1) : d177 p ≤ (2 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4847 (p : Pattern) (guard : d4299 p = 1) : d178 p ≤ (2 : Int) + d28 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4845 p hg
    simpa only [d4299, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4846 p hg
    simpa only [d4299, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4848 (p : Pattern) (guard : d4432 p = 1) : d179 p ≤ (2 : Int) + d28 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d4432, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d4432, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4849 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d10 p := by
  change (4 : Int) ≤ (2 : Int) + 10
  decide
theorem compare4850 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4851 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4850 p hg
    simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4852 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4851 p hg
    simpa only [d43, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d43, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4853 (p : Pattern) (guard : d1 p = 1) : d180 p ≤ (2 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d180, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4834 p hg
    simpa only [d180, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d180, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4852 p hg
    simpa only [d180, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4854 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d11 p := by
  change (6 : Int) ≤ (2 : Int) + 11
  decide
theorem compare4855 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4854 p hg
    simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4856 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4854 p hg
    simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4855 p hg
    simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4857 (p : Pattern) (guard : d1 p = 1) : d173 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4856 p hg
    simpa only [d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d173, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4858 (p : Pattern) (guard : d1 p = 1) : d181 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d181, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4857 p hg
    simpa only [d181, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d181, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1790 p hg
    simpa only [d181, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4859 (p : Pattern) (guard : d1 p = 1) : d182 p ≤ (2 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d182, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4853 p hg
    simpa only [d182, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d182, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4858 p hg
    simpa only [d182, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4860 (p : Pattern) (guard : d0 p = 1) : d184 p ≤ (2 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4861 (p : Pattern) (guard : d4299 p = 1) : d185 p ≤ (2 : Int) + d64 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4859 p hg
    simpa only [d4299, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4860 p hg
    simpa only [d4299, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4862 (p : Pattern) (guard : d4432 p = 1) : d186 p ≤ (2 : Int) + d64 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d4432, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4861 p hg
    simpa only [d4432, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4863 (p : Pattern) (guard : d4432 p = 1) : d187 p ≤ (2 : Int) + d4433 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d187, d4433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4848 p hg
    simpa only [d187, d4433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d187, d4433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4862 p hg
    simpa only [d187, d4433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4864 (p : Pattern) (guard : d0 p = 1) : d189 p ≤ (2 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4865 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d2 p := by
  change (4 : Int) ≤ (2 : Int) + 2
  decide
theorem compare4866 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4867 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4866 p hg
    simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4868 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (2 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4869 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4868 p hg
    simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4870 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d6 p := by
  change (8 : Int) ≤ (2 : Int) + 6
  decide
theorem compare4871 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d190, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d190, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4872 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d191, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4873 (p : Pattern) (guard : d1 p = 1) : d192 p ≤ (2 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4872 p hg
    simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d192, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4874 (p : Pattern) (guard : d1 p = 1) : d193 p ≤ (2 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d193, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4872 p hg
    simpa only [d193, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d193, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4873 p hg
    simpa only [d193, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4875 (p : Pattern) (guard : d1 p = 1) : d194 p ≤ (2 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d194, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d194, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d194, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4874 p hg
    simpa only [d194, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4876 (p : Pattern) (guard : d1 p = 1) : d195 p ≤ (2 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d195, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4875 p hg
    simpa only [d195, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d195, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d195, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4877 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4878 (p : Pattern) (guard : d4299 p = 1) : d196 p ≤ (2 : Int) + d80 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4876 p hg
    simpa only [d4299, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4877 p hg
    simpa only [d4299, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4879 (p : Pattern) (guard : d4432 p = 1) : d197 p ≤ (2 : Int) + d80 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4864 p hg
    simpa only [d4432, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4878 p hg
    simpa only [d4432, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4880 (p : Pattern) (guard : d0 p = 1) : d200 p ≤ (2 : Int) + d84 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4881 (p : Pattern) (guard : d1 p = 1) : d201 p ≤ (2 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d201, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4874 p hg
    simpa only [d201, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d201, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d201, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4882 (p : Pattern) (guard : d1 p = 1) : d202 p ≤ (2 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d202, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d202, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d202, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d202, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4883 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d84 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4884 (p : Pattern) (guard : d4299 p = 1) : d203 p ≤ (2 : Int) + d84 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4882 p hg
    simpa only [d4299, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4883 p hg
    simpa only [d4299, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4885 (p : Pattern) (guard : d4432 p = 1) : d204 p ≤ (2 : Int) + d84 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4880 p hg
    simpa only [d4432, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d4432, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4886 (p : Pattern) (guard : d4432 p = 1) : d205 p ≤ (2 : Int) + d4445 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d205, d4445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4879 p hg
    simpa only [d205, d4445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d205, d4445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4885 p hg
    simpa only [d205, d4445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4887 (p : Pattern) (guard : d4432 p = 1) : d206 p ≤ (2 : Int) + d4446 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d206, d4446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4863 p hg
    simpa only [d206, d4446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d206, d4446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d206, d4446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4888 (p : Pattern) (guard : d4432 p = 1) : d207 p ≤ (2 : Int) + d4447 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d207, d4447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d207, d4447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d207, d4447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d207, d4447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4889 (p : Pattern) (guard : d4432 p = 1) : d208 p ≤ (2 : Int) + d4448 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d208, d4448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4887 p hg
    simpa only [d208, d4448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d208, d4448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4888 p hg
    simpa only [d208, d4448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4890 (p : Pattern) (guard : d4432 p = 1) : d209 p ≤ (2 : Int) + d4449 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d209, d4449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d209, d4449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d209, d4449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d209, d4449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4891 (p : Pattern) (guard : d4432 p = 1) : d210 p ≤ (2 : Int) + d4450 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d210, d4450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d210, d4450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d210, d4450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4890 p hg
    simpa only [d210, d4450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4892 (p : Pattern) (guard : d0 p = 1) : d214 p ≤ (2 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4893 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d12 p := by
  change (3 : Int) ≤ (2 : Int) + 12
  decide
theorem compare4894 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4895 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4896 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4897 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d140, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d140, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4898 (p : Pattern) (guard : d1 p = 1) : d215 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4899 (p : Pattern) (guard : d1 p = 1) : d216 p ≤ (2 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d216, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4897 p hg
    simpa only [d216, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d216, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4898 p hg
    simpa only [d216, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
