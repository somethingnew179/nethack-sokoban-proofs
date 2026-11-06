/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6160 (p : Pattern) (guard : d4618 p = 1) : d771 p ≤ (2 : Int) + d4657 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d771, d4657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6150 p hg
    simpa only [d4618, d771, d4657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d771, d4657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6159 p hg
    simpa only [d4618, d771, d4657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6161 (p : Pattern) (guard : d4618 p = 1) : d777 p ≤ (2 : Int) + d4658 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d777, d4658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6116 p hg
    simpa only [d777, d4658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d777, d4658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6160 p hg
    simpa only [d777, d4658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6162 (p : Pattern) (guard : d0 p = 1) : d242 p ≤ (2 : Int) + d241 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6163 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2214 p hg
    simpa only [d109, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6164 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (2 : Int) + d62 p := by
  omega
theorem compare6165 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (2 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d136, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6164 p hg
    simpa only [d136, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6166 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d241 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6167 (p : Pattern) (guard : d4395 p = 1) : d137 p ≤ (2 : Int) + d241 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6165 p hg
    simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6166 p hg
    simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6168 (p : Pattern) (guard : d4617 p = 1) : d243 p ≤ (2 : Int) + d241 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6162 p hg
    simpa only [d4617, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6167 p hg
    simpa only [d4617, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6169 (p : Pattern) (guard : d4618 p = 1) : d778 p ≤ (2 : Int) + d4659 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d778, d4659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6168 p hg
    simpa only [d4618, d778, d4659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d778, d4659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d4618, d778, d4659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6170 (p : Pattern) (guard : d0 p = 1) : d245 p ≤ (2 : Int) + d211 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6171 (p : Pattern) (guard : d4395 p = 1) : d154 p ≤ (2 : Int) + d211 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d4395, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d4395, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6172 (p : Pattern) (guard : d4617 p = 1) : d246 p ≤ (2 : Int) + d211 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6170 p hg
    simpa only [d4617, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6171 p hg
    simpa only [d4617, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6173 (p : Pattern) (guard : d4618 p = 1) : d779 p ≤ (2 : Int) + d4652 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d779, d4652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6172 p hg
    simpa only [d4618, d779, d4652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d779, d4652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6102 p hg
    simpa only [d4618, d779, d4652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6174 (p : Pattern) (guard : d4618 p = 1) : d780 p ≤ (2 : Int) + d4660 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d780, d4660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6169 p hg
    simpa only [d780, d4660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d780, d4660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6173 p hg
    simpa only [d780, d4660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6175 (p : Pattern) (guard : d4618 p = 1) : d781 p ≤ (2 : Int) + d4661 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d781, d4661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6161 p hg
    simpa only [d781, d4661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d781, d4661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6174 p hg
    simpa only [d781, d4661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6176 (p : Pattern) (guard : d0 p = 1) : d253 p ≤ (2 : Int) + d252 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6177 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (2 : Int) + d26 p := by
  omega
theorem compare6178 (p : Pattern) (guard : d1 p = 1) : d254 p ≤ (2 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d254, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d254, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d254, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6177 p hg
    simpa only [d254, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6179 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d252 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6180 (p : Pattern) (guard : d4395 p = 1) : d255 p ≤ (2 : Int) + d252 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6178 p hg
    simpa only [d4395, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6179 p hg
    simpa only [d4395, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6181 (p : Pattern) (guard : d4617 p = 1) : d256 p ≤ (2 : Int) + d252 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6176 p hg
    simpa only [d4617, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6180 p hg
    simpa only [d4617, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6182 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d136 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6183 (p : Pattern) (guard : d4618 p = 1) : d782 p ≤ (2 : Int) + d4662 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d782, d4662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6181 p hg
    simpa only [d4618, d782, d4662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d782, d4662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6182 p hg
    simpa only [d4618, d782, d4662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6184 (p : Pattern) (guard : d4618 p = 1) : d783 p ≤ (2 : Int) + d4663 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d783, d4663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6183 p hg
    simpa only [d783, d4663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d783, d4663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6173 p hg
    simpa only [d783, d4663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6185 (p : Pattern) (guard : d4618 p = 1) : d784 p ≤ (2 : Int) + d4664 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d784, d4664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6184 p hg
    simpa only [d784, d4664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d784, d4664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d784, d4664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6186 (p : Pattern) (guard : d4618 p = 1) : d785 p ≤ (2 : Int) + d4665 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d785, d4665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6175 p hg
    simpa only [d785, d4665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d785, d4665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6185 p hg
    simpa only [d785, d4665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6187 (p : Pattern) (guard : d4618 p = 1) : d786 p ≤ (2 : Int) + d4666 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d786, d4666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6158 p hg
    simpa only [d786, d4666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d786, d4666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6186 p hg
    simpa only [d786, d4666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6188 (p : Pattern) (guard : d4618 p = 1) : d787 p ≤ (2 : Int) + d4667 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d787, d4667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d787, d4667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d787, d4667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6187 p hg
    simpa only [d787, d4667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6189 (p : Pattern) (guard : d4618 p = 1) : d788 p ≤ (2 : Int) + d4668 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d788, d4668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6145 p hg
    simpa only [d788, d4668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d788, d4668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6188 p hg
    simpa only [d788, d4668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6190 (p : Pattern) (guard : d4618 p = 1) : d789 p ≤ (2 : Int) + d4669 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d789, d4669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6125 p hg
    simpa only [d789, d4669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d789, d4669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6189 p hg
    simpa only [d789, d4669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6191 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6192 (p : Pattern) (guard : d4117 p = 1) : d713 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6191 p hg
    simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6193 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d85 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6194 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6193 p hg
    simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6195 (p : Pattern) (guard : d4117 p = 1) : d715 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6192 p hg
    simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6194 p hg
    simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6196 (p : Pattern) (guard : d4117 p = 1) : d716 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5333 p hg
    simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6195 p hg
    simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6197 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6198 (p : Pattern) (guard : d4117 p = 1) : d717 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6197 p hg
    simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6199 (p : Pattern) (guard : d4117 p = 1) : d718 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6198 p hg
    simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6194 p hg
    simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6200 (p : Pattern) (guard : d4117 p = 1) : d719 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4607 p hg
    simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6201 (p : Pattern) (guard : d4117 p = 1) : d720 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6200 p hg
    simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6202 (p : Pattern) (guard : d4117 p = 1) : d721 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6199 p hg
    simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6201 p hg
    simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6203 (p : Pattern) (guard : d4117 p = 1) : d722 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6196 p hg
    simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6202 p hg
    simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6204 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6205 (p : Pattern) (guard : d4117 p = 1) : d726 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6204 p hg
    simpa only [d4117, d726, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6206 (p : Pattern) (guard : d4117 p = 1) : d727 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6205 p hg
    simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6194 p hg
    simpa only [d727, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6207 (p : Pattern) (guard : d4117 p = 1) : d728 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5348 p hg
    simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6206 p hg
    simpa only [d728, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6208 (p : Pattern) (guard : d4117 p = 1) : d729 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6206 p hg
    simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d729, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6209 (p : Pattern) (guard : d4117 p = 1) : d730 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6207 p hg
    simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6208 p hg
    simpa only [d730, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6210 (p : Pattern) (guard : d4117 p = 1) : d731 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6203 p hg
    simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6209 p hg
    simpa only [d731, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6211 (p : Pattern) (guard : d4117 p = 1) : d735 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5361 p hg
    simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6206 p hg
    simpa only [d735, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6212 (p : Pattern) (guard : d4117 p = 1) : d736 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6195 p hg
    simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6201 p hg
    simpa only [d736, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6213 (p : Pattern) (guard : d4117 p = 1) : d737 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6211 p hg
    simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6212 p hg
    simpa only [d737, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6214 (p : Pattern) (guard : d4117 p = 1) : d738 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6206 p hg
    simpa only [d738, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6215 (p : Pattern) (guard : d4117 p = 1) : d739 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6214 p hg
    simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6208 p hg
    simpa only [d739, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6216 (p : Pattern) (guard : d4117 p = 1) : d740 p ≤ (0 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6213 p hg
    simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6215 p hg
    simpa only [d740, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6217 (p : Pattern) (guard : d4117 p = 1) : d741 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6216 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6218 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6219 (p : Pattern) (guard : d4117 p = 1) : d745 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6218 p hg
    simpa only [d4117, d745, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6220 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6221 (p : Pattern) (guard : d4117 p = 1) : d746 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6220 p hg
    simpa only [d4117, d746, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6222 (p : Pattern) (guard : d4117 p = 1) : d747 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6219 p hg
    simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d747, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6223 (p : Pattern) (guard : d4117 p = 1) : d748 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d748, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6224 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6225 (p : Pattern) (guard : d4117 p = 1) : d749 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6224 p hg
    simpa only [d4117, d749, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6226 (p : Pattern) (guard : d4117 p = 1) : d750 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6225 p hg
    simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6221 p hg
    simpa only [d750, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6227 (p : Pattern) (guard : d4117 p = 1) : d751 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6226 p hg
    simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d751, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6228 (p : Pattern) (guard : d4117 p = 1) : d752 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6223 p hg
    simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6227 p hg
    simpa only [d752, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6229 (p : Pattern) (guard : d4117 p = 1) : d755 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d755, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6230 (p : Pattern) (guard : d4117 p = 1) : d756 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6222 p hg
    simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d756, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6231 (p : Pattern) (guard : d4117 p = 1) : d757 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6230 p hg
    simpa only [d757, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6232 (p : Pattern) (guard : d4117 p = 1) : d758 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6228 p hg
    simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6231 p hg
    simpa only [d758, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6233 (p : Pattern) (guard : d4117 p = 1) : d759 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6232 p hg
    simpa only [d759, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6234 (p : Pattern) (guard : d4117 p = 1) : d760 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6217 p hg
    simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6233 p hg
    simpa only [d760, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6235 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6236 (p : Pattern) (guard : d4117 p = 1) : d717 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6235 p hg
    simpa only [d4117, d717, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6237 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d185 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6238 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6237 p hg
    simpa only [d4117, d714, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6239 (p : Pattern) (guard : d4117 p = 1) : d718 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6236 p hg
    simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6238 p hg
    simpa only [d718, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6240 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d196 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6241 (p : Pattern) (guard : d4117 p = 1) : d761 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6240 p hg
    simpa only [d4117, d761, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6242 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d203 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6243 (p : Pattern) (guard : d4117 p = 1) : d762 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d4117, d762, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6244 (p : Pattern) (guard : d4117 p = 1) : d763 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6241 p hg
    simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d763, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6245 (p : Pattern) (guard : d4117 p = 1) : d764 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6239 p hg
    simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d764, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6246 (p : Pattern) (guard : d4117 p = 1) : d765 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d765, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6247 (p : Pattern) (guard : d4117 p = 1) : d766 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6245 p hg
    simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6246 p hg
    simpa only [d766, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6248 (p : Pattern) (guard : d4117 p = 1) : d767 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6213 p hg
    simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d767, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6249 (p : Pattern) (guard : d4117 p = 1) : d768 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6248 p hg
    simpa only [d768, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6250 (p : Pattern) (guard : d4117 p = 1) : d771 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6220 p hg
    simpa only [d4117, d771, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6251 (p : Pattern) (guard : d4117 p = 1) : d772 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6219 p hg
    simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d772, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6252 (p : Pattern) (guard : d4117 p = 1) : d773 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5422 p hg
    simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6251 p hg
    simpa only [d773, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6253 (p : Pattern) (guard : d4117 p = 1) : d774 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6225 p hg
    simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d774, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6254 (p : Pattern) (guard : d4117 p = 1) : d775 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6253 p hg
    simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d775, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6255 (p : Pattern) (guard : d4117 p = 1) : d776 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6252 p hg
    simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6254 p hg
    simpa only [d776, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6256 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6257 (p : Pattern) (guard : d4117 p = 1) : d753 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d4117, d753, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6258 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d238 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6259 (p : Pattern) (guard : d4117 p = 1) : d771 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6258 p hg
    simpa only [d4117, d771, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6260 (p : Pattern) (guard : d4117 p = 1) : d777 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6257 p hg
    simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d777, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6261 (p : Pattern) (guard : d4117 p = 1) : d778 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4672 p hg
    simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6220 p hg
    simpa only [d4117, d778, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6262 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d248 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6263 (p : Pattern) (guard : d4117 p = 1) : d779 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6262 p hg
    simpa only [d4117, d779, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6264 (p : Pattern) (guard : d4117 p = 1) : d780 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6263 p hg
    simpa only [d780, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6265 (p : Pattern) (guard : d4117 p = 1) : d781 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6260 p hg
    simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6264 p hg
    simpa only [d781, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6266 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d259 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6267 (p : Pattern) (guard : d4117 p = 1) : d782 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6266 p hg
    simpa only [d4117, d782, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6268 (p : Pattern) (guard : d4117 p = 1) : d783 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6267 p hg
    simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6263 p hg
    simpa only [d783, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6269 (p : Pattern) (guard : d4117 p = 1) : d784 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6268 p hg
    simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d784, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6270 (p : Pattern) (guard : d4117 p = 1) : d785 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6265 p hg
    simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6269 p hg
    simpa only [d785, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6271 (p : Pattern) (guard : d4117 p = 1) : d786 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6255 p hg
    simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d786, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6272 (p : Pattern) (guard : d4117 p = 1) : d787 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6210 p hg
    simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6271 p hg
    simpa only [d787, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6273 (p : Pattern) (guard : d4117 p = 1) : d788 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6249 p hg
    simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6272 p hg
    simpa only [d788, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6274 (p : Pattern) (guard : d4117 p = 1) : d789 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6234 p hg
    simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6273 p hg
    simpa only [d789, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6275 (p : Pattern) (guard : d0 p = 1) : d376 p ≤ (2 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6276 (p : Pattern) (guard : d4117 p = 1) : d710 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6275 p hg
    simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6277 (p : Pattern) (guard : d0 p = 1) : d391 p ≤ (2 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6278 (p : Pattern) (guard : d4117 p = 1) : d711 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6277 p hg
    simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6279 (p : Pattern) (guard : d4117 p = 1) : d712 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6278 p hg
    simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6280 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (2 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6281 (p : Pattern) (guard : d4117 p = 1) : d713 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6280 p hg
    simpa only [d4117, d713, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6282 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d85 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6283 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (2 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6282 p hg
    simpa only [d4117, d714, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6284 (p : Pattern) (guard : d4117 p = 1) : d715 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6281 p hg
    simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6283 p hg
    simpa only [d715, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6285 (p : Pattern) (guard : d4117 p = 1) : d716 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6279 p hg
    simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d716, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6286 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (2 : Int) + d81 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6287 (p : Pattern) (guard : d4117 p = 1) : d717 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6286 p hg
    simpa only [d4117, d717, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6288 (p : Pattern) (guard : d4117 p = 1) : d718 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6287 p hg
    simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6283 p hg
    simpa only [d718, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6289 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (2 : Int) + d92 p := by
  omega
theorem compare6290 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d93 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6291 (p : Pattern) (guard : d4117 p = 1) : d719 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6289 p hg
    simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6290 p hg
    simpa only [d4117, d719, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6292 (p : Pattern) (guard : d4117 p = 1) : d95 p ≤ (2 : Int) + d95 p := by
  omega
theorem compare6293 (p : Pattern) (guard : d4117 p = 1) : d720 p ≤ (2 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6292 p hg
    simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6294 (p : Pattern) (guard : d4117 p = 1) : d721 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6288 p hg
    simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d721, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6295 (p : Pattern) (guard : d4117 p = 1) : d722 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6285 p hg
    simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d722, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6296 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (2 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6297 (p : Pattern) (guard : d4117 p = 1) : d723 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6296 p hg
    simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6298 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (2 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6299 (p : Pattern) (guard : d4117 p = 1) : d724 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6298 p hg
    simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
