/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5040 (p : Pattern) (guard : d917 p = 1) : d651 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5031 p hg
    simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5039 p hg
    simpa only [d651, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5041 (p : Pattern) (guard : d917 p = 1) : d652 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5023 p hg
    simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d652, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5042 (p : Pattern) (guard : d917 p = 1) : d653 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5028 p hg
    simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d653, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5043 (p : Pattern) (guard : d917 p = 1) : d654 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5041 p hg
    simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5042 p hg
    simpa only [d654, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5044 (p : Pattern) (guard : d917 p = 1) : d655 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5043 p hg
    simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d655, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5045 (p : Pattern) (guard : d917 p = 1) : d656 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5044 p hg
    simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d656, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5046 (p : Pattern) (guard : d917 p = 1) : d657 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5040 p hg
    simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5045 p hg
    simpa only [d657, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5047 (p : Pattern) (guard : d917 p = 1) : d658 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5018 p hg
    simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5046 p hg
    simpa only [d658, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5048 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5049 (p : Pattern) (guard : d917 p = 1) : d28 p ≤ (2 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5048 p hg
    simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5050 (p : Pattern) (guard : d917 p = 1) : d29 p ≤ (2 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5049 p hg
    simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5051 (p : Pattern) (guard : d917 p = 1) : d14 p ≤ (2 : Int) + d8 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5052 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5053 (p : Pattern) (guard : d917 p = 1) : d28 p ≤ (2 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d28, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d917, d28, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d28, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5052 p hg
    simpa only [d917, d28, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5054 (p : Pattern) (guard : d917 p = 1) : d30 p ≤ (2 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5053 p hg
    simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5055 (p : Pattern) (guard : d917 p = 1) : d31 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d31, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d31, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d31, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d31, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5056 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5057 (p : Pattern) (guard : d917 p = 1) : d587 p ≤ (2 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5058 (p : Pattern) (guard : d917 p = 1) : d588 p ≤ (2 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5059 (p : Pattern) (guard : d917 p = 1) : d589 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5060 (p : Pattern) (guard : d917 p = 1) : d259 p ≤ (2 : Int) + d9 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4527 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5061 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5062 (p : Pattern) (guard : d917 p = 1) : d587 p ≤ (2 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d587, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d917, d587, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d587, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5061 p hg
    simpa only [d917, d587, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5063 (p : Pattern) (guard : d917 p = 1) : d590 p ≤ (2 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d590, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d590, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d590, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d590, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5064 (p : Pattern) (guard : d917 p = 1) : d591 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d591, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d591, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d591, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d591, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5065 (p : Pattern) (guard : d917 p = 1) : d592 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d592, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5059 p hg
    simpa only [d592, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d592, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d592, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5066 (p : Pattern) (guard : d917 p = 1) : d593 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d593, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d593, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d593, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5065 p hg
    simpa only [d593, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5067 (p : Pattern) (guard : d0 p = 1) : d597 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5068 (p : Pattern) (guard : d918 p = 1) : d598 p ≤ (2 : Int) + d63 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5066 p hg
    simpa only [d918, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d918, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5069 (p : Pattern) (guard : d917 p = 1) : d599 p ≤ (2 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d599, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d599, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d599, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d599, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5070 (p : Pattern) (guard : d917 p = 1) : d600 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d600, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d600, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d600, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d600, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5071 (p : Pattern) (guard : d917 p = 1) : d601 p ≤ (2 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5072 (p : Pattern) (guard : d917 p = 1) : d602 p ≤ (2 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5071 p hg
    simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5073 (p : Pattern) (guard : d917 p = 1) : d603 p ≤ (2 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d603, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d603, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d603, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d603, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5074 (p : Pattern) (guard : d917 p = 1) : d604 p ≤ (2 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d604, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d604, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d604, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d604, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5075 (p : Pattern) (guard : d917 p = 1) : d605 p ≤ (2 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d605, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5072 p hg
    simpa only [d605, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d605, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5074 p hg
    simpa only [d605, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5076 (p : Pattern) (guard : d917 p = 1) : d606 p ≤ (2 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d606, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5075 p hg
    simpa only [d606, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d606, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d606, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5077 (p : Pattern) (guard : d917 p = 1) : d607 p ≤ (2 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d607, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5070 p hg
    simpa only [d607, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d607, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5076 p hg
    simpa only [d607, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5078 (p : Pattern) (guard : d917 p = 1) : d608 p ≤ (2 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d608, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5070 p hg
    simpa only [d608, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d608, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d608, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5079 (p : Pattern) (guard : d0 p = 1) : d616 p ≤ (2 : Int) + d237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5080 (p : Pattern) (guard : d918 p = 1) : d617 p ≤ (2 : Int) + d237 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5078 p hg
    simpa only [d918, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d918, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5081 (p : Pattern) (guard : d918 p = 1) : d618 p ≤ (2 : Int) + d1177 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d618, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5068 p hg
    simpa only [d618, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d618, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5080 p hg
    simpa only [d618, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5082 (p : Pattern) (guard : d917 p = 1) : d619 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d619, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5066 p hg
    simpa only [d619, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d619, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d619, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5083 (p : Pattern) (guard : d0 p = 1) : d620 p ≤ (2 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5084 (p : Pattern) (guard : d918 p = 1) : d621 p ≤ (2 : Int) + d69 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5082 p hg
    simpa only [d918, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5083 p hg
    simpa only [d918, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5085 (p : Pattern) (guard : d917 p = 1) : d622 p ≤ (2 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d622, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d622, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d622, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d622, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5086 (p : Pattern) (guard : d0 p = 1) : d623 p ≤ (2 : Int) + d240 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5087 (p : Pattern) (guard : d918 p = 1) : d624 p ≤ (2 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d918, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5086 p hg
    simpa only [d918, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5088 (p : Pattern) (guard : d918 p = 1) : d625 p ≤ (2 : Int) + d1178 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d625, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d625, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d625, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5087 p hg
    simpa only [d625, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5089 (p : Pattern) (guard : d918 p = 1) : d626 p ≤ (2 : Int) + d1179 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d626, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d626, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d626, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5088 p hg
    simpa only [d626, d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5090 (p : Pattern) (guard : d0 p = 1) : d609 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5091 (p : Pattern) (guard : d918 p = 1) : d627 p ≤ (2 : Int) + d65 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d918, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d918, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5092 (p : Pattern) (guard : d918 p = 1) : d628 p ≤ (2 : Int) + d1180 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d628, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5088 p hg
    simpa only [d628, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d628, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d628, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5093 (p : Pattern) (guard : d918 p = 1) : d629 p ≤ (2 : Int) + d1181 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d629, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5089 p hg
    simpa only [d629, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d629, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5092 p hg
    simpa only [d629, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5094 (p : Pattern) (guard : d917 p = 1) : d630 p ≤ (2 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5071 p hg
    simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5095 (p : Pattern) (guard : d917 p = 1) : d631 p ≤ (2 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d631, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d631, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d631, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d631, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5096 (p : Pattern) (guard : d917 p = 1) : d632 p ≤ (2 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d632, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5094 p hg
    simpa only [d632, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d632, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5095 p hg
    simpa only [d632, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5097 (p : Pattern) (guard : d917 p = 1) : d633 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d633, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5075 p hg
    simpa only [d633, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d633, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d633, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5098 (p : Pattern) (guard : d917 p = 1) : d634 p ≤ (2 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d634, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5066 p hg
    simpa only [d634, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d634, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5097 p hg
    simpa only [d634, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5099 (p : Pattern) (guard : d917 p = 1) : d635 p ≤ (2 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d635, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5066 p hg
    simpa only [d635, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d635, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5098 p hg
    simpa only [d635, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5100 (p : Pattern) (guard : d0 p = 1) : d640 p ≤ (2 : Int) + d246 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5101 (p : Pattern) (guard : d918 p = 1) : d641 p ≤ (2 : Int) + d246 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5099 p hg
    simpa only [d918, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5100 p hg
    simpa only [d918, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5102 (p : Pattern) (guard : d918 p = 1) : d642 p ≤ (2 : Int) + d1182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d642, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5101 p hg
    simpa only [d642, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d642, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d642, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5103 (p : Pattern) (guard : d917 p = 1) : d643 p ≤ (2 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d643, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d643, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d643, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d643, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5104 (p : Pattern) (guard : d917 p = 1) : d644 p ≤ (2 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d644, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5103 p hg
    simpa only [d644, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d644, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5097 p hg
    simpa only [d644, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5105 (p : Pattern) (guard : d917 p = 1) : d645 p ≤ (2 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5104 p hg
    simpa only [d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d645, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5106 (p : Pattern) (guard : d0 p = 1) : d648 p ≤ (2 : Int) + d249 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5107 (p : Pattern) (guard : d918 p = 1) : d649 p ≤ (2 : Int) + d249 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d918, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5106 p hg
    simpa only [d918, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5108 (p : Pattern) (guard : d918 p = 1) : d650 p ≤ (2 : Int) + d1183 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d650, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5107 p hg
    simpa only [d650, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d650, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d650, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5109 (p : Pattern) (guard : d918 p = 1) : d651 p ≤ (2 : Int) + d1184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d651, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5102 p hg
    simpa only [d651, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d651, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5108 p hg
    simpa only [d651, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5110 (p : Pattern) (guard : d917 p = 1) : d652 p ≤ (2 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d652, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5098 p hg
    simpa only [d652, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d652, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d652, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5111 (p : Pattern) (guard : d0 p = 1) : d653 p ≤ (2 : Int) + d253 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5112 (p : Pattern) (guard : d918 p = 1) : d654 p ≤ (2 : Int) + d253 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d918, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d918, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d918, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5111 p hg
    simpa only [d918, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5113 (p : Pattern) (guard : d918 p = 1) : d655 p ≤ (2 : Int) + d1185 p := by
  cases selected : p 134 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d655, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5112 p hg
    simpa only [d655, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d655, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d655, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5114 (p : Pattern) (guard : d918 p = 1) : d656 p ≤ (2 : Int) + d1186 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d656, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5113 p hg
    simpa only [d656, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d656, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d656, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5115 (p : Pattern) (guard : d918 p = 1) : d657 p ≤ (2 : Int) + d1187 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d657, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5109 p hg
    simpa only [d657, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d657, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d657, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5116 (p : Pattern) (guard : d918 p = 1) : d658 p ≤ (2 : Int) + d1188 p := by
  cases selected : p 108 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d658, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d658, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d658, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5115 p hg
    simpa only [d658, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5117 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5118 (p : Pattern) (guard : d917 p = 1) : d14 p ≤ (2 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5117 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5119 (p : Pattern) (guard : d917 p = 1) : d30 p ≤ (2 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5049 p hg
    simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5120 (p : Pattern) (guard : d917 p = 1) : d31 p ≤ (2 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5121 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5122 (p : Pattern) (guard : d917 p = 1) : d259 p ≤ (2 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5121 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5123 (p : Pattern) (guard : d917 p = 1) : d590 p ≤ (2 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5122 p hg
    simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5124 (p : Pattern) (guard : d917 p = 1) : d591 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5125 (p : Pattern) (guard : d917 p = 1) : d592 p ≤ (2 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5059 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5124 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5126 (p : Pattern) (guard : d917 p = 1) : d593 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5120 p hg
    simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5125 p hg
    simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5127 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5128 (p : Pattern) (guard : d917 p = 1) : d32 p ≤ (2 : Int) + d8 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5127 p hg
    simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5129 (p : Pattern) (guard : d917 p = 1) : d32 p ≤ (2 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5052 p hg
    simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5130 (p : Pattern) (guard : d917 p = 1) : d32 p ≤ (2 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5128 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5129 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5131 (p : Pattern) (guard : d917 p = 1) : d33 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5130 p hg
    simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5132 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5133 (p : Pattern) (guard : d917 p = 1) : d594 p ≤ (2 : Int) + d9 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5132 p hg
    simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5134 (p : Pattern) (guard : d917 p = 1) : d594 p ≤ (2 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5061 p hg
    simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5135 (p : Pattern) (guard : d917 p = 1) : d594 p ≤ (2 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5133 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5134 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5136 (p : Pattern) (guard : d917 p = 1) : d595 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5130 p hg
    simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5135 p hg
    simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5137 (p : Pattern) (guard : d917 p = 1) : d596 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5124 p hg
    simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5136 p hg
    simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5138 (p : Pattern) (guard : d917 p = 1) : d597 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5131 p hg
    simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5137 p hg
    simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5139 (p : Pattern) (guard : d917 p = 1) : d598 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5140 (p : Pattern) (guard : d917 p = 1) : d599 p ≤ (2 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5141 (p : Pattern) (guard : d917 p = 1) : d600 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5120 p hg
    simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5142 (p : Pattern) (guard : d917 p = 1) : d603 p ≤ (2 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5143 (p : Pattern) (guard : d917 p = 1) : d604 p ≤ (2 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5142 p hg
    simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5144 (p : Pattern) (guard : d917 p = 1) : d605 p ≤ (2 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5072 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5143 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5145 (p : Pattern) (guard : d917 p = 1) : d606 p ≤ (2 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5144 p hg
    simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5146 (p : Pattern) (guard : d917 p = 1) : d607 p ≤ (2 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5141 p hg
    simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5145 p hg
    simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5147 (p : Pattern) (guard : d917 p = 1) : d608 p ≤ (2 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5141 p hg
    simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5146 p hg
    simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5148 (p : Pattern) (guard : d917 p = 1) : d609 p ≤ (2 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5135 p hg
    simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5149 (p : Pattern) (guard : d917 p = 1) : d610 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5131 p hg
    simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5150 (p : Pattern) (guard : d917 p = 1) : d611 p ≤ (2 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5130 p hg
    simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5135 p hg
    simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5151 (p : Pattern) (guard : d917 p = 1) : d612 p ≤ (2 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5130 p hg
    simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5150 p hg
    simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5152 (p : Pattern) (guard : d917 p = 1) : d613 p ≤ (2 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5143 p hg
    simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5151 p hg
    simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5153 (p : Pattern) (guard : d917 p = 1) : d614 p ≤ (2 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5152 p hg
    simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5154 (p : Pattern) (guard : d917 p = 1) : d615 p ≤ (2 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5149 p hg
    simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5153 p hg
    simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5155 (p : Pattern) (guard : d917 p = 1) : d616 p ≤ (2 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5149 p hg
    simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5154 p hg
    simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5156 (p : Pattern) (guard : d917 p = 1) : d617 p ≤ (2 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5147 p hg
    simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5155 p hg
    simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5157 (p : Pattern) (guard : d917 p = 1) : d618 p ≤ (2 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5139 p hg
    simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5156 p hg
    simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5158 (p : Pattern) (guard : d917 p = 1) : d619 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5159 (p : Pattern) (guard : d917 p = 1) : d620 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5160 (p : Pattern) (guard : d917 p = 1) : d621 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5158 p hg
    simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5159 p hg
    simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5161 (p : Pattern) (guard : d917 p = 1) : d622 p ≤ (2 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5146 p hg
    simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5162 (p : Pattern) (guard : d917 p = 1) : d623 p ≤ (2 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5154 p hg
    simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5163 (p : Pattern) (guard : d917 p = 1) : d624 p ≤ (2 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5161 p hg
    simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5164 (p : Pattern) (guard : d917 p = 1) : d625 p ≤ (2 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5160 p hg
    simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5165 (p : Pattern) (guard : d917 p = 1) : d626 p ≤ (2 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5157 p hg
    simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5166 (p : Pattern) (guard : d917 p = 1) : d627 p ≤ (2 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5167 (p : Pattern) (guard : d917 p = 1) : d628 p ≤ (2 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5168 (p : Pattern) (guard : d917 p = 1) : d629 p ≤ (2 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5167 p hg
    simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5169 (p : Pattern) (guard : d917 p = 1) : d631 p ≤ (2 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5142 p hg
    simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5170 (p : Pattern) (guard : d917 p = 1) : d632 p ≤ (2 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5094 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5171 (p : Pattern) (guard : d917 p = 1) : d633 p ≤ (2 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5144 p hg
    simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5170 p hg
    simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5172 (p : Pattern) (guard : d917 p = 1) : d634 p ≤ (2 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5173 (p : Pattern) (guard : d917 p = 1) : d635 p ≤ (2 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5172 p hg
    simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5174 (p : Pattern) (guard : d917 p = 1) : d636 p ≤ (2 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5150 p hg
    simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5135 p hg
    simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5175 (p : Pattern) (guard : d917 p = 1) : d637 p ≤ (2 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5174 p hg
    simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5176 (p : Pattern) (guard : d917 p = 1) : d638 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5152 p hg
    simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5175 p hg
    simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5177 (p : Pattern) (guard : d917 p = 1) : d639 p ≤ (2 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5176 p hg
    simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5178 (p : Pattern) (guard : d917 p = 1) : d640 p ≤ (2 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5177 p hg
    simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5179 (p : Pattern) (guard : d917 p = 1) : d641 p ≤ (2 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5178 p hg
    simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
