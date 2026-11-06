/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7140 (p : Pattern) (guard : d0 p = 1) : d807 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7141 (p : Pattern) (guard : d1 p = 1) : d808 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d808, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d808, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d808, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d808, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7142 (p : Pattern) (guard : d1 p = 1) : d809 p ≤ (2 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d809, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d809, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d809, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d809, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7143 (p : Pattern) (guard : d1 p = 1) : d810 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d810, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7141 p hg
    simpa only [d810, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d810, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7142 p hg
    simpa only [d810, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7144 (p : Pattern) (guard : d4299 p = 1) : d811 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d811, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7143 p hg
    simpa only [d4299, d811, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d811, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4754 p hg
    simpa only [d4299, d811, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7145 (p : Pattern) (guard : d4432 p = 1) : d812 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7140 p hg
    simpa only [d4432, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7144 p hg
    simpa only [d4432, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7146 (p : Pattern) (guard : d4432 p = 1) : d813 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d813, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7139 p hg
    simpa only [d813, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d813, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7145 p hg
    simpa only [d813, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7147 (p : Pattern) (guard : d4432 p = 1) : d814 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7135 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7146 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7148 (p : Pattern) (guard : d0 p = 1) : d815 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7149 (p : Pattern) (guard : d4432 p = 1) : d816 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7148 p hg
    simpa only [d4432, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7138 p hg
    simpa only [d4432, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7150 (p : Pattern) (guard : d0 p = 1) : d817 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7151 (p : Pattern) (guard : d4432 p = 1) : d818 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7150 p hg
    simpa only [d4432, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7144 p hg
    simpa only [d4432, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7152 (p : Pattern) (guard : d4432 p = 1) : d819 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d819, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7149 p hg
    simpa only [d819, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d819, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d819, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7153 (p : Pattern) (guard : d0 p = 1) : d820 p ≤ (2 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7154 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (2 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7155 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (2 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7154 p hg
    simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7156 (p : Pattern) (guard : d4299 p = 1) : d93 p ≤ (2 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7155 p hg
    simpa only [d4299, d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4761 p hg
    simpa only [d4299, d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7157 (p : Pattern) (guard : d4432 p = 1) : d821 p ≤ (2 : Int) + d92 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7153 p hg
    simpa only [d4432, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7156 p hg
    simpa only [d4432, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7158 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (2 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7159 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7160 (p : Pattern) (guard : d4299 p = 1) : d12 p ≤ (2 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7159 p hg
    simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4299, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7161 (p : Pattern) (guard : d4432 p = 1) : d95 p ≤ (2 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7160 p hg
    simpa only [d4432, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7162 (p : Pattern) (guard : d4432 p = 1) : d822 p ≤ (2 : Int) + d4730 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d822, d4730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7157 p hg
    simpa only [d822, d4730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d822, d4730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7161 p hg
    simpa only [d822, d4730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7163 (p : Pattern) (guard : d4432 p = 1) : d823 p ≤ (2 : Int) + d4731 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d823, d4731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7152 p hg
    simpa only [d823, d4731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d823, d4731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7162 p hg
    simpa only [d823, d4731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7164 (p : Pattern) (guard : d4432 p = 1) : d824 p ≤ (2 : Int) + d4732 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d824, d4732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7147 p hg
    simpa only [d824, d4732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d824, d4732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7163 p hg
    simpa only [d824, d4732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7165 (p : Pattern) (guard : d0 p = 1) : d825 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7166 (p : Pattern) (guard : d4299 p = 1) : d826 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d826, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d4299, d826, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d826, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4746 p hg
    simpa only [d4299, d826, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7167 (p : Pattern) (guard : d4432 p = 1) : d827 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7165 p hg
    simpa only [d4432, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d4432, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7168 (p : Pattern) (guard : d0 p = 1) : d828 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7169 (p : Pattern) (guard : d4432 p = 1) : d829 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d4432, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7133 p hg
    simpa only [d4432, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7170 (p : Pattern) (guard : d4432 p = 1) : d830 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d830, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d830, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d830, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7169 p hg
    simpa only [d830, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7171 (p : Pattern) (guard : d0 p = 1) : d831 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7172 (p : Pattern) (guard : d4432 p = 1) : d832 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7171 p hg
    simpa only [d4432, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7138 p hg
    simpa only [d4432, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7173 (p : Pattern) (guard : d4432 p = 1) : d833 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d833, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7172 p hg
    simpa only [d833, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d833, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7145 p hg
    simpa only [d833, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7174 (p : Pattern) (guard : d4432 p = 1) : d834 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7170 p hg
    simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7175 (p : Pattern) (guard : d4432 p = 1) : d835 p ≤ (2 : Int) + d4733 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d835, d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d835, d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d835, d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d835, d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7176 (p : Pattern) (guard : d4432 p = 1) : d836 p ≤ (2 : Int) + d4734 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d836, d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d836, d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d836, d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7175 p hg
    simpa only [d836, d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7177 (p : Pattern) (guard : d4432 p = 1) : d837 p ≤ (2 : Int) + d4735 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d837, d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d837, d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d837, d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7176 p hg
    simpa only [d837, d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7178 (p : Pattern) (guard : d0 p = 1) : d838 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7179 (p : Pattern) (guard : d4432 p = 1) : d839 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d4432, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d4432, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7180 (p : Pattern) (guard : d0 p = 1) : d840 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7181 (p : Pattern) (guard : d4432 p = 1) : d841 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7180 p hg
    simpa only [d4432, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7133 p hg
    simpa only [d4432, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7182 (p : Pattern) (guard : d4432 p = 1) : d842 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d842, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7179 p hg
    simpa only [d842, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d842, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7181 p hg
    simpa only [d842, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7183 (p : Pattern) (guard : d0 p = 1) : d843 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7184 (p : Pattern) (guard : d4432 p = 1) : d844 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7183 p hg
    simpa only [d4432, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7138 p hg
    simpa only [d4432, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7185 (p : Pattern) (guard : d4432 p = 1) : d845 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d845, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d845, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d845, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7145 p hg
    simpa only [d845, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7186 (p : Pattern) (guard : d4432 p = 1) : d846 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7182 p hg
    simpa only [d846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7185 p hg
    simpa only [d846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7187 (p : Pattern) (guard : d4432 p = 1) : d847 p ≤ (2 : Int) + d4731 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d847, d4731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7146 p hg
    simpa only [d847, d4731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d847, d4731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7162 p hg
    simpa only [d847, d4731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7188 (p : Pattern) (guard : d4432 p = 1) : d848 p ≤ (2 : Int) + d4732 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d848, d4732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7186 p hg
    simpa only [d848, d4732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d848, d4732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7187 p hg
    simpa only [d848, d4732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7189 (p : Pattern) (guard : d4432 p = 1) : d849 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7148 p hg
    simpa only [d4432, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d4432, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7190 (p : Pattern) (guard : d4432 p = 1) : d850 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7150 p hg
    simpa only [d4432, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7133 p hg
    simpa only [d4432, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7191 (p : Pattern) (guard : d4432 p = 1) : d851 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d851, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7189 p hg
    simpa only [d851, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d851, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7190 p hg
    simpa only [d851, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7192 (p : Pattern) (guard : d4432 p = 1) : d852 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7191 p hg
    simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7193 (p : Pattern) (guard : d4432 p = 1) : d853 p ≤ (2 : Int) + d4734 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d853, d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7192 p hg
    simpa only [d853, d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d853, d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7175 p hg
    simpa only [d853, d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7194 (p : Pattern) (guard : d4432 p = 1) : d854 p ≤ (2 : Int) + d4735 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d854, d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d854, d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d854, d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7193 p hg
    simpa only [d854, d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7195 (p : Pattern) (guard : d4432 p = 1) : d855 p ≤ (2 : Int) + d4735 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7177 p hg
    simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7194 p hg
    simpa only [d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7196 (p : Pattern) (guard : d0 p = 1) : d856 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7197 (p : Pattern) (guard : d1 p = 1) : d857 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4775 p hg
    simpa only [d857, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d857, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4808 p hg
    simpa only [d857, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7198 (p : Pattern) (guard : d4299 p = 1) : d858 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d858, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7197 p hg
    simpa only [d4299, d858, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d858, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d4299, d858, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7199 (p : Pattern) (guard : d4432 p = 1) : d859 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7196 p hg
    simpa only [d4432, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7198 p hg
    simpa only [d4432, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7200 (p : Pattern) (guard : d0 p = 1) : d860 p ≤ (2 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7201 (p : Pattern) (guard : d1 p = 1) : d861 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2214 p hg
    simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7202 (p : Pattern) (guard : d1 p = 1) : d862 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d862, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d862, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d862, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7201 p hg
    simpa only [d862, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7203 (p : Pattern) (guard : d1 p = 1) : d863 p ≤ (2 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d863, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d863, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d863, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d863, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7204 (p : Pattern) (guard : d1 p = 1) : d864 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d864, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7202 p hg
    simpa only [d864, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d864, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7203 p hg
    simpa only [d864, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7205 (p : Pattern) (guard : d4299 p = 1) : d865 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d865, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7204 p hg
    simpa only [d4299, d865, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d865, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d4299, d865, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7206 (p : Pattern) (guard : d4432 p = 1) : d866 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7200 p hg
    simpa only [d4432, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7205 p hg
    simpa only [d4432, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7207 (p : Pattern) (guard : d4432 p = 1) : d867 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d867, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7199 p hg
    simpa only [d867, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d867, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7206 p hg
    simpa only [d867, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7208 (p : Pattern) (guard : d0 p = 1) : d868 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7209 (p : Pattern) (guard : d1 p = 1) : d869 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d869, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d869, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d869, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4808 p hg
    simpa only [d869, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7210 (p : Pattern) (guard : d4299 p = 1) : d870 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d870, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7209 p hg
    simpa only [d4299, d870, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d870, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d4299, d870, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7211 (p : Pattern) (guard : d4432 p = 1) : d871 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7208 p hg
    simpa only [d4432, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7210 p hg
    simpa only [d4432, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7212 (p : Pattern) (guard : d0 p = 1) : d872 p ≤ (2 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7213 (p : Pattern) (guard : d1 p = 1) : d873 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d873, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d873, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d873, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7214 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (2 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d153, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d153, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7215 (p : Pattern) (guard : d1 p = 1) : d874 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d874, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7213 p hg
    simpa only [d874, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d874, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7214 p hg
    simpa only [d874, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7216 (p : Pattern) (guard : d4299 p = 1) : d875 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d875, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d4299, d875, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d875, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d4299, d875, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7217 (p : Pattern) (guard : d4432 p = 1) : d876 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7212 p hg
    simpa only [d4432, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7216 p hg
    simpa only [d4432, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7218 (p : Pattern) (guard : d4432 p = 1) : d877 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d877, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7211 p hg
    simpa only [d877, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d877, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7217 p hg
    simpa only [d877, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7219 (p : Pattern) (guard : d4432 p = 1) : d878 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7207 p hg
    simpa only [d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7218 p hg
    simpa only [d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7220 (p : Pattern) (guard : d0 p = 1) : d879 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7221 (p : Pattern) (guard : d4432 p = 1) : d880 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d4432, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7210 p hg
    simpa only [d4432, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7222 (p : Pattern) (guard : d4432 p = 1) : d881 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d881, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d881, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d881, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7217 p hg
    simpa only [d881, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7223 (p : Pattern) (guard : d0 p = 1) : d160 p ≤ (2 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7224 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7225 (p : Pattern) (guard : d4299 p = 1) : d12 p ≤ (2 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7224 p hg
    simpa only [d4299, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4299, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7226 (p : Pattern) (guard : d4432 p = 1) : d161 p ≤ (2 : Int) + d160 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7223 p hg
    simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7225 p hg
    simpa only [d4432, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7227 (p : Pattern) (guard : d4432 p = 1) : d162 p ≤ (2 : Int) + d4737 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d162, d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7226 p hg
    simpa only [d162, d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d162, d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d162, d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7228 (p : Pattern) (guard : d4432 p = 1) : d882 p ≤ (2 : Int) + d4738 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d882, d4738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d882, d4738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d882, d4738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d882, d4738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7229 (p : Pattern) (guard : d4432 p = 1) : d883 p ≤ (2 : Int) + d4739 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d883, d4739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7219 p hg
    simpa only [d883, d4739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d883, d4739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d883, d4739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7230 (p : Pattern) (guard : d0 p = 1) : d884 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7231 (p : Pattern) (guard : d4432 p = 1) : d885 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7230 p hg
    simpa only [d4432, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7198 p hg
    simpa only [d4432, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7232 (p : Pattern) (guard : d0 p = 1) : d886 p ≤ (2 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7233 (p : Pattern) (guard : d4432 p = 1) : d887 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7232 p hg
    simpa only [d4432, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7205 p hg
    simpa only [d4432, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7234 (p : Pattern) (guard : d4432 p = 1) : d888 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d888, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7231 p hg
    simpa only [d888, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d888, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7233 p hg
    simpa only [d888, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7235 (p : Pattern) (guard : d0 p = 1) : d889 p ≤ (2 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7236 (p : Pattern) (guard : d4432 p = 1) : d890 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7235 p hg
    simpa only [d4432, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7210 p hg
    simpa only [d4432, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7237 (p : Pattern) (guard : d4432 p = 1) : d891 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d891, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d891, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d891, d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7217 p hg
    simpa only [d891, d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7238 (p : Pattern) (guard : d4432 p = 1) : d892 p ≤ (2 : Int) + d4736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7234 p hg
    simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7237 p hg
    simpa only [d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7239 (p : Pattern) (guard : d4432 p = 1) : d893 p ≤ (2 : Int) + d4740 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d893, d4740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7237 p hg
    simpa only [d893, d4740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d893, d4740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d893, d4740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7240 (p : Pattern) (guard : d4432 p = 1) : d894 p ≤ (2 : Int) + d4741 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d894, d4741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7238 p hg
    simpa only [d894, d4741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d894, d4741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7239 p hg
    simpa only [d894, d4741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7241 (p : Pattern) (guard : d4432 p = 1) : d895 p ≤ (2 : Int) + d4742 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d895, d4742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7229 p hg
    simpa only [d895, d4742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d895, d4742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7240 p hg
    simpa only [d895, d4742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7242 (p : Pattern) (guard : d4432 p = 1) : d896 p ≤ (2 : Int) + d4743 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d896, d4743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7177 p hg
    simpa only [d896, d4743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d896, d4743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d896, d4743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7243 (p : Pattern) (guard : d4432 p = 1) : d897 p ≤ (2 : Int) + d4744 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d897, d4744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7195 p hg
    simpa only [d897, d4744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d897, d4744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7242 p hg
    simpa only [d897, d4744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7244 (p : Pattern) (guard : d0 p = 1) : d898 p ≤ (2 : Int) + d189 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7245 (p : Pattern) (guard : d1 p = 1) : d899 p ≤ (2 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d899, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d899, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d899, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4875 p hg
    simpa only [d899, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7246 (p : Pattern) (guard : d4299 p = 1) : d900 p ≤ (2 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d900, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7245 p hg
    simpa only [d4299, d900, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d900, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4877 p hg
    simpa only [d4299, d900, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7247 (p : Pattern) (guard : d4432 p = 1) : d901 p ≤ (2 : Int) + d189 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7244 p hg
    simpa only [d4432, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7246 p hg
    simpa only [d4432, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7248 (p : Pattern) (guard : d0 p = 1) : d902 p ≤ (2 : Int) + d200 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7249 (p : Pattern) (guard : d1 p = 1) : d903 p ≤ (2 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d903, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d903, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d903, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6134 p hg
    simpa only [d903, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7250 (p : Pattern) (guard : d4299 p = 1) : d904 p ≤ (2 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d904, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7249 p hg
    simpa only [d4299, d904, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d904, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4883 p hg
    simpa only [d4299, d904, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7251 (p : Pattern) (guard : d4432 p = 1) : d905 p ≤ (2 : Int) + d200 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7248 p hg
    simpa only [d4432, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7250 p hg
    simpa only [d4432, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7252 (p : Pattern) (guard : d4432 p = 1) : d906 p ≤ (2 : Int) + d4745 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d906, d4745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7247 p hg
    simpa only [d906, d4745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d906, d4745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7251 p hg
    simpa only [d906, d4745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7253 (p : Pattern) (guard : d4432 p = 1) : d907 p ≤ (2 : Int) + d4746 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d907, d4746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7191 p hg
    simpa only [d907, d4746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d907, d4746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7252 p hg
    simpa only [d907, d4746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7254 (p : Pattern) (guard : d4432 p = 1) : d908 p ≤ (2 : Int) + d4747 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d908, d4747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7252 p hg
    simpa only [d908, d4747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d908, d4747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d908, d4747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7255 (p : Pattern) (guard : d4432 p = 1) : d909 p ≤ (2 : Int) + d4748 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d909, d4748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7253 p hg
    simpa only [d909, d4748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d909, d4748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7254 p hg
    simpa only [d909, d4748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7256 (p : Pattern) (guard : d4432 p = 1) : d910 p ≤ (2 : Int) + d4749 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d910, d4749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d910, d4749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d910, d4749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7255 p hg
    simpa only [d910, d4749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7257 (p : Pattern) (guard : d4432 p = 1) : d911 p ≤ (2 : Int) + d4750 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d911, d4750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7177 p hg
    simpa only [d911, d4750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d911, d4750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7256 p hg
    simpa only [d911, d4750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7258 (p : Pattern) (guard : d0 p = 1) : d912 p ≤ (2 : Int) + d214 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7259 (p : Pattern) (guard : d1 p = 1) : d863 p ≤ (2 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d863, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d863, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d863, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d863, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7260 (p : Pattern) (guard : d1 p = 1) : d864 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d864, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7202 p hg
    simpa only [d864, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d864, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7259 p hg
    simpa only [d864, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7261 (p : Pattern) (guard : d4299 p = 1) : d865 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d865, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7260 p hg
    simpa only [d4299, d865, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d865, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d4299, d865, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7262 (p : Pattern) (guard : d4432 p = 1) : d913 p ≤ (2 : Int) + d214 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7258 p hg
    simpa only [d4432, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7261 p hg
    simpa only [d4432, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7263 (p : Pattern) (guard : d4432 p = 1) : d914 p ≤ (2 : Int) + d4751 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d914, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7199 p hg
    simpa only [d914, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d914, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7262 p hg
    simpa only [d914, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7264 (p : Pattern) (guard : d0 p = 1) : d915 p ≤ (2 : Int) + d214 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7265 (p : Pattern) (guard : d1 p = 1) : d874 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d874, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7213 p hg
    simpa only [d874, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d874, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d874, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7266 (p : Pattern) (guard : d4299 p = 1) : d875 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d875, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7265 p hg
    simpa only [d4299, d875, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d875, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d4299, d875, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7267 (p : Pattern) (guard : d4432 p = 1) : d916 p ≤ (2 : Int) + d214 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7264 p hg
    simpa only [d4432, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d4432, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7268 (p : Pattern) (guard : d4432 p = 1) : d917 p ≤ (2 : Int) + d4751 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d917, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7211 p hg
    simpa only [d917, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d917, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7267 p hg
    simpa only [d917, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7269 (p : Pattern) (guard : d4432 p = 1) : d918 p ≤ (2 : Int) + d4751 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7263 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7270 (p : Pattern) (guard : d4432 p = 1) : d919 p ≤ (2 : Int) + d4751 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d919, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d919, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d919, d4751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7267 p hg
    simpa only [d919, d4751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7271 (p : Pattern) (guard : d4432 p = 1) : d920 p ≤ (2 : Int) + d4752 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d920, d4752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d920, d4752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d920, d4752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d920, d4752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7272 (p : Pattern) (guard : d4432 p = 1) : d921 p ≤ (2 : Int) + d4753 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d921, d4753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7269 p hg
    simpa only [d921, d4753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d921, d4753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7271 p hg
    simpa only [d921, d4753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7273 (p : Pattern) (guard : d1 p = 1) : d922 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d922, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2201 p hg
    simpa only [d922, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d922, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4808 p hg
    simpa only [d922, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7274 (p : Pattern) (guard : d4299 p = 1) : d923 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d923, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d4299, d923, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d923, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d4299, d923, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7275 (p : Pattern) (guard : d4432 p = 1) : d924 p ≤ (2 : Int) + d114 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7230 p hg
    simpa only [d4432, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7274 p hg
    simpa only [d4432, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7276 (p : Pattern) (guard : d1 p = 1) : d925 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d925, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d925, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d925, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2215 p hg
    simpa only [d925, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7277 (p : Pattern) (guard : d1 p = 1) : d926 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d926, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7276 p hg
    simpa only [d926, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d926, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2217 p hg
    simpa only [d926, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7278 (p : Pattern) (guard : d4299 p = 1) : d927 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d927, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7277 p hg
    simpa only [d4299, d927, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d927, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d4299, d927, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7279 (p : Pattern) (guard : d4432 p = 1) : d928 p ≤ (2 : Int) + d214 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7264 p hg
    simpa only [d4432, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d4432, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
