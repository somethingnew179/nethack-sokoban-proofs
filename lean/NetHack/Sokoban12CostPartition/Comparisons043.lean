/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6020 (p : Pattern) (guard : d1233 p = 1) : d64 p ≤ (0 : Int) + d673 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d64, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6005 p hg
    simpa only [d64, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d64, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d64, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6021 (p : Pattern) (guard : d1233 p = 1) : d55 p ≤ (0 : Int) + d674 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5999 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6022 (p : Pattern) (guard : d1233 p = 1) : d106 p ≤ (0 : Int) + d675 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d106, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5990 p hg
    simpa only [d106, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d106, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d106, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6023 (p : Pattern) (guard : d1233 p = 1) : d119 p ≤ (0 : Int) + d676 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d119, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5987 p hg
    simpa only [d119, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d119, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5999 p hg
    simpa only [d119, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6024 (p : Pattern) (guard : d1233 p = 1) : d120 p ≤ (0 : Int) + d677 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d120, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5987 p hg
    simpa only [d120, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d120, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6023 p hg
    simpa only [d120, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6025 (p : Pattern) (guard : d1233 p = 1) : d119 p ≤ (0 : Int) + d678 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d119, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d119, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d119, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d119, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6026 (p : Pattern) (guard : d1233 p = 1) : d120 p ≤ (0 : Int) + d679 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d120, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d120, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d120, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d120, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6027 (p : Pattern) (guard : d1233 p = 1) : d120 p ≤ (0 : Int) + d680 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6024 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6026 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6028 (p : Pattern) (guard : d1233 p = 1) : d121 p ≤ (0 : Int) + d681 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d121, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6027 p hg
    simpa only [d121, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d121, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d121, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6029 (p : Pattern) (guard : d1233 p = 1) : d122 p ≤ (0 : Int) + d682 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d122, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6022 p hg
    simpa only [d122, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d122, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6028 p hg
    simpa only [d122, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6030 (p : Pattern) (guard : d1233 p = 1) : d179 p ≤ (0 : Int) + d683 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d179, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6022 p hg
    simpa only [d179, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d179, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6029 p hg
    simpa only [d179, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6031 (p : Pattern) (guard : d1233 p = 1) : d65 p ≤ (0 : Int) + d684 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d65, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d65, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d65, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6016 p hg
    simpa only [d65, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6032 (p : Pattern) (guard : d1233 p = 1) : d109 p ≤ (0 : Int) + d685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d109, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6011 p hg
    simpa only [d109, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d109, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d109, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6033 (p : Pattern) (guard : d1233 p = 1) : d125 p ≤ (0 : Int) + d686 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d125, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6010 p hg
    simpa only [d125, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d125, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6016 p hg
    simpa only [d125, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6034 (p : Pattern) (guard : d1233 p = 1) : d126 p ≤ (0 : Int) + d687 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d126, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6010 p hg
    simpa only [d126, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d126, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d126, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6035 (p : Pattern) (guard : d1233 p = 1) : d127 p ≤ (0 : Int) + d688 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d127, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6026 p hg
    simpa only [d127, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d127, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6034 p hg
    simpa only [d127, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6036 (p : Pattern) (guard : d1233 p = 1) : d128 p ≤ (0 : Int) + d689 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d128, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6035 p hg
    simpa only [d128, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d128, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d128, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6037 (p : Pattern) (guard : d1233 p = 1) : d129 p ≤ (0 : Int) + d690 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d129, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6032 p hg
    simpa only [d129, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d129, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6036 p hg
    simpa only [d129, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6038 (p : Pattern) (guard : d1233 p = 1) : d237 p ≤ (0 : Int) + d691 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d237, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6032 p hg
    simpa only [d237, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d237, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6037 p hg
    simpa only [d237, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6039 (p : Pattern) (guard : d1233 p = 1) : d238 p ≤ (0 : Int) + d692 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d238, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6030 p hg
    simpa only [d238, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d238, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6038 p hg
    simpa only [d238, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6040 (p : Pattern) (guard : d1233 p = 1) : d239 p ≤ (0 : Int) + d693 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d239, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6020 p hg
    simpa only [d239, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d239, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6039 p hg
    simpa only [d239, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6041 (p : Pattern) (guard : d1233 p = 1) : d68 p ≤ (0 : Int) + d694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d68, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6005 p hg
    simpa only [d68, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d68, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d68, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6042 (p : Pattern) (guard : d1233 p = 1) : d69 p ≤ (0 : Int) + d695 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d69, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d69, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d69, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d69, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6043 (p : Pattern) (guard : d1233 p = 1) : d70 p ≤ (0 : Int) + d696 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d70, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6041 p hg
    simpa only [d70, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d70, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6042 p hg
    simpa only [d70, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6044 (p : Pattern) (guard : d1233 p = 1) : d181 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d181, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6029 p hg
    simpa only [d181, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d181, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d181, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6045 (p : Pattern) (guard : d1233 p = 1) : d240 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d240, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6037 p hg
    simpa only [d240, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d240, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d240, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6046 (p : Pattern) (guard : d1233 p = 1) : d241 p ≤ (0 : Int) + d699 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d241, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6044 p hg
    simpa only [d241, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d241, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6045 p hg
    simpa only [d241, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6047 (p : Pattern) (guard : d1233 p = 1) : d242 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d242, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d242, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d242, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6046 p hg
    simpa only [d242, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6048 (p : Pattern) (guard : d1233 p = 1) : d243 p ≤ (0 : Int) + d701 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d243, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6040 p hg
    simpa only [d243, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d243, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6047 p hg
    simpa only [d243, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6049 (p : Pattern) (guard : d1233 p = 1) : d66 p ≤ (0 : Int) + d702 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d66, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d66, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d66, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d66, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6050 (p : Pattern) (guard : d1233 p = 1) : d244 p ≤ (0 : Int) + d703 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d244, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6047 p hg
    simpa only [d244, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d244, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d244, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6051 (p : Pattern) (guard : d1233 p = 1) : d245 p ≤ (0 : Int) + d704 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d245, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6048 p hg
    simpa only [d245, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d245, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6050 p hg
    simpa only [d245, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6052 (p : Pattern) (guard : d1233 p = 1) : d137 p ≤ (0 : Int) + d705 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d137, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6023 p hg
    simpa only [d137, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d137, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5999 p hg
    simpa only [d137, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6053 (p : Pattern) (guard : d1233 p = 1) : d137 p ≤ (0 : Int) + d706 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d137, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d137, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d137, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d137, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6054 (p : Pattern) (guard : d1233 p = 1) : d137 p ≤ (0 : Int) + d707 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6052 p hg
    simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6053 p hg
    simpa only [d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6055 (p : Pattern) (guard : d1233 p = 1) : d139 p ≤ (0 : Int) + d708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d139, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6027 p hg
    simpa only [d139, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d139, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6054 p hg
    simpa only [d139, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6056 (p : Pattern) (guard : d1233 p = 1) : d153 p ≤ (0 : Int) + d709 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d153, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6005 p hg
    simpa only [d153, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d153, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6055 p hg
    simpa only [d153, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6057 (p : Pattern) (guard : d1233 p = 1) : d186 p ≤ (0 : Int) + d710 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d186, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6005 p hg
    simpa only [d186, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d186, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6056 p hg
    simpa only [d186, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6058 (p : Pattern) (guard : d1233 p = 1) : d143 p ≤ (0 : Int) + d711 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d143, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d143, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d143, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6016 p hg
    simpa only [d143, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6059 (p : Pattern) (guard : d1233 p = 1) : d144 p ≤ (0 : Int) + d712 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d144, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6053 p hg
    simpa only [d144, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d144, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d144, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6060 (p : Pattern) (guard : d1233 p = 1) : d146 p ≤ (0 : Int) + d713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d146, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6035 p hg
    simpa only [d146, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d146, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d146, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6061 (p : Pattern) (guard : d1233 p = 1) : d155 p ≤ (0 : Int) + d714 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d155, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d155, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d155, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6060 p hg
    simpa only [d155, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6062 (p : Pattern) (guard : d1233 p = 1) : d246 p ≤ (0 : Int) + d715 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d246, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d246, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d246, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d246, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6063 (p : Pattern) (guard : d1233 p = 1) : d247 p ≤ (0 : Int) + d716 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d247, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6057 p hg
    simpa only [d247, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d247, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6062 p hg
    simpa only [d247, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6064 (p : Pattern) (guard : d1233 p = 1) : d248 p ≤ (0 : Int) + d717 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d248, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6063 p hg
    simpa only [d248, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d248, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d248, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6065 (p : Pattern) (guard : d1233 p = 1) : d138 p ≤ (0 : Int) + d718 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d138, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5990 p hg
    simpa only [d138, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d138, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6054 p hg
    simpa only [d138, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6066 (p : Pattern) (guard : d1233 p = 1) : d140 p ≤ (0 : Int) + d719 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d140, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6065 p hg
    simpa only [d140, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d140, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6055 p hg
    simpa only [d140, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6067 (p : Pattern) (guard : d1233 p = 1) : d188 p ≤ (0 : Int) + d720 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d188, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6066 p hg
    simpa only [d188, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d188, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d188, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6068 (p : Pattern) (guard : d1233 p = 1) : d145 p ≤ (0 : Int) + d721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d145, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6011 p hg
    simpa only [d145, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d145, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d145, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6069 (p : Pattern) (guard : d1233 p = 1) : d147 p ≤ (0 : Int) + d722 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d147, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6068 p hg
    simpa only [d147, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d147, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6060 p hg
    simpa only [d147, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6070 (p : Pattern) (guard : d1233 p = 1) : d249 p ≤ (0 : Int) + d723 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d249, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6069 p hg
    simpa only [d249, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d249, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d249, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6071 (p : Pattern) (guard : d1233 p = 1) : d250 p ≤ (0 : Int) + d724 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d250, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6067 p hg
    simpa only [d250, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d250, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6070 p hg
    simpa only [d250, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6072 (p : Pattern) (guard : d1233 p = 1) : d251 p ≤ (0 : Int) + d725 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d251, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6071 p hg
    simpa only [d251, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d251, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d251, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6073 (p : Pattern) (guard : d1233 p = 1) : d252 p ≤ (0 : Int) + d726 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d252, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d252, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d252, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6072 p hg
    simpa only [d252, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6074 (p : Pattern) (guard : d1233 p = 1) : d191 p ≤ (0 : Int) + d727 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d191, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6056 p hg
    simpa only [d191, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d191, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d191, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6075 (p : Pattern) (guard : d1233 p = 1) : d253 p ≤ (0 : Int) + d728 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d253, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d253, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d253, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d253, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6076 (p : Pattern) (guard : d1233 p = 1) : d254 p ≤ (0 : Int) + d729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d254, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6074 p hg
    simpa only [d254, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d254, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6075 p hg
    simpa only [d254, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6077 (p : Pattern) (guard : d1233 p = 1) : d255 p ≤ (0 : Int) + d730 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d255, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6076 p hg
    simpa only [d255, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d255, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d255, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6078 (p : Pattern) (guard : d1233 p = 1) : d256 p ≤ (0 : Int) + d731 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d256, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6077 p hg
    simpa only [d256, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d256, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d256, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6079 (p : Pattern) (guard : d1233 p = 1) : d257 p ≤ (0 : Int) + d732 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d257, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6073 p hg
    simpa only [d257, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d257, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6078 p hg
    simpa only [d257, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6080 (p : Pattern) (guard : d1233 p = 1) : d258 p ≤ (0 : Int) + d733 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d258, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6051 p hg
    simpa only [d258, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d258, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6079 p hg
    simpa only [d258, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6081 (p : Pattern) (guard : d917 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare6082 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6083 (p : Pattern) (guard : d917 p = 1) : d10 p ≤ (0 : Int) + d9 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare297 p hg
    simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6082 p hg
    simpa only [d917, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6084 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (0 : Int) + d923 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d11, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6081 p hg
    simpa only [d11, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d11, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6083 p hg
    simpa only [d11, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6085 (p : Pattern) (guard : d917 p = 1) : d12 p ≤ (0 : Int) + d924 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d12, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d12, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d12, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d12, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6086 (p : Pattern) (guard : d917 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare6087 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6088 (p : Pattern) (guard : d917 p = 1) : d59 p ≤ (0 : Int) + d58 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare299 p hg
    simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6087 p hg
    simpa only [d917, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6089 (p : Pattern) (guard : d917 p = 1) : d60 p ≤ (0 : Int) + d925 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d60, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6086 p hg
    simpa only [d60, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d60, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6088 p hg
    simpa only [d60, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6090 (p : Pattern) (guard : d917 p = 1) : d61 p ≤ (0 : Int) + d926 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d61, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d61, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d61, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d61, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6091 (p : Pattern) (guard : d917 p = 1) : d62 p ≤ (0 : Int) + d927 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d62, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d62, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d62, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6090 p hg
    simpa only [d62, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6092 (p : Pattern) (guard : d917 p = 1) : d63 p ≤ (0 : Int) + d928 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d63, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6085 p hg
    simpa only [d63, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d63, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6091 p hg
    simpa only [d63, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6093 (p : Pattern) (guard : d917 p = 1) : d64 p ≤ (0 : Int) + d929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d64, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d64, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d64, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6092 p hg
    simpa only [d64, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6094 (p : Pattern) (guard : d917 p = 1) : d65 p ≤ (0 : Int) + d936 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d65, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d65, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d65, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d65, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6095 (p : Pattern) (guard : d917 p = 1) : d109 p ≤ (0 : Int) + d937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d109, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6085 p hg
    simpa only [d109, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d109, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d109, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6096 (p : Pattern) (guard : d917 p = 1) : d125 p ≤ (0 : Int) + d938 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d125, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d125, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d125, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d125, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6097 (p : Pattern) (guard : d917 p = 1) : d126 p ≤ (0 : Int) + d939 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d126, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d126, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d126, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d126, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6098 (p : Pattern) (guard : d917 p = 1) : d127 p ≤ (0 : Int) + d940 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d127, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1170 p hg
    simpa only [d127, d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d127, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6097 p hg
    simpa only [d127, d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6099 (p : Pattern) (guard : d917 p = 1) : d128 p ≤ (0 : Int) + d941 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d128, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6098 p hg
    simpa only [d128, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d128, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d128, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6100 (p : Pattern) (guard : d917 p = 1) : d129 p ≤ (0 : Int) + d942 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d129, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6095 p hg
    simpa only [d129, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d129, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6099 p hg
    simpa only [d129, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6101 (p : Pattern) (guard : d917 p = 1) : d237 p ≤ (0 : Int) + d943 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d237, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6095 p hg
    simpa only [d237, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d237, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6100 p hg
    simpa only [d237, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6102 (p : Pattern) (guard : d917 p = 1) : d238 p ≤ (0 : Int) + d944 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d238, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d238, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d238, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6101 p hg
    simpa only [d238, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6103 (p : Pattern) (guard : d917 p = 1) : d239 p ≤ (0 : Int) + d945 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d239, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6093 p hg
    simpa only [d239, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d239, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6102 p hg
    simpa only [d239, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6104 (p : Pattern) (guard : d917 p = 1) : d69 p ≤ (0 : Int) + d947 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d69, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6092 p hg
    simpa only [d69, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d69, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d69, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6105 (p : Pattern) (guard : d917 p = 1) : d70 p ≤ (0 : Int) + d948 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d70, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d70, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d70, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6104 p hg
    simpa only [d70, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6106 (p : Pattern) (guard : d917 p = 1) : d240 p ≤ (0 : Int) + d950 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d240, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6100 p hg
    simpa only [d240, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d240, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d240, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6107 (p : Pattern) (guard : d917 p = 1) : d241 p ≤ (0 : Int) + d951 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d241, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1180 p hg
    simpa only [d241, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d241, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6106 p hg
    simpa only [d241, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6108 (p : Pattern) (guard : d917 p = 1) : d242 p ≤ (0 : Int) + d952 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d242, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6105 p hg
    simpa only [d242, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d242, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6107 p hg
    simpa only [d242, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6109 (p : Pattern) (guard : d917 p = 1) : d243 p ≤ (0 : Int) + d953 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d243, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6103 p hg
    simpa only [d243, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d243, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6108 p hg
    simpa only [d243, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6110 (p : Pattern) (guard : d917 p = 1) : d66 p ≤ (0 : Int) + d954 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d66, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d66, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d66, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d66, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6111 (p : Pattern) (guard : d917 p = 1) : d244 p ≤ (0 : Int) + d955 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d244, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6108 p hg
    simpa only [d244, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d244, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d244, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6112 (p : Pattern) (guard : d917 p = 1) : d245 p ≤ (0 : Int) + d956 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d245, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6109 p hg
    simpa only [d245, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d245, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6111 p hg
    simpa only [d245, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6113 (p : Pattern) (guard : d917 p = 1) : d143 p ≤ (0 : Int) + d961 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d143, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d143, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d143, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d143, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6114 (p : Pattern) (guard : d917 p = 1) : d144 p ≤ (0 : Int) + d962 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d144, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1189 p hg
    simpa only [d144, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d144, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6113 p hg
    simpa only [d144, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6115 (p : Pattern) (guard : d917 p = 1) : d146 p ≤ (0 : Int) + d963 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d146, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6098 p hg
    simpa only [d146, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d146, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6114 p hg
    simpa only [d146, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6116 (p : Pattern) (guard : d917 p = 1) : d155 p ≤ (0 : Int) + d964 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d155, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6092 p hg
    simpa only [d155, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d155, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6115 p hg
    simpa only [d155, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6117 (p : Pattern) (guard : d917 p = 1) : d246 p ≤ (0 : Int) + d965 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d246, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6092 p hg
    simpa only [d246, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d246, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6116 p hg
    simpa only [d246, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6118 (p : Pattern) (guard : d917 p = 1) : d247 p ≤ (0 : Int) + d966 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d247, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d247, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d247, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6117 p hg
    simpa only [d247, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6119 (p : Pattern) (guard : d917 p = 1) : d248 p ≤ (0 : Int) + d967 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d248, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6118 p hg
    simpa only [d248, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d248, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d248, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6120 (p : Pattern) (guard : d917 p = 1) : d145 p ≤ (0 : Int) + d971 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d145, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6085 p hg
    simpa only [d145, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d145, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6114 p hg
    simpa only [d145, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6121 (p : Pattern) (guard : d917 p = 1) : d147 p ≤ (0 : Int) + d972 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d147, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6120 p hg
    simpa only [d147, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d147, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6115 p hg
    simpa only [d147, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6122 (p : Pattern) (guard : d917 p = 1) : d249 p ≤ (0 : Int) + d973 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d249, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6121 p hg
    simpa only [d249, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d249, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d249, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6123 (p : Pattern) (guard : d917 p = 1) : d250 p ≤ (0 : Int) + d974 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d250, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1198 p hg
    simpa only [d250, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d250, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6122 p hg
    simpa only [d250, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6124 (p : Pattern) (guard : d917 p = 1) : d251 p ≤ (0 : Int) + d975 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d251, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6123 p hg
    simpa only [d251, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d251, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d251, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6125 (p : Pattern) (guard : d917 p = 1) : d252 p ≤ (0 : Int) + d976 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d252, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6119 p hg
    simpa only [d252, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d252, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6124 p hg
    simpa only [d252, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6126 (p : Pattern) (guard : d917 p = 1) : d253 p ≤ (0 : Int) + d978 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d253, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6116 p hg
    simpa only [d253, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d253, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d253, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6127 (p : Pattern) (guard : d917 p = 1) : d254 p ≤ (0 : Int) + d979 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d254, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1203 p hg
    simpa only [d254, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d254, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6126 p hg
    simpa only [d254, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6128 (p : Pattern) (guard : d917 p = 1) : d255 p ≤ (0 : Int) + d980 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d255, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6127 p hg
    simpa only [d255, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d255, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d255, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6129 (p : Pattern) (guard : d917 p = 1) : d256 p ≤ (0 : Int) + d981 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d256, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6128 p hg
    simpa only [d256, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d256, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d256, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6130 (p : Pattern) (guard : d917 p = 1) : d257 p ≤ (0 : Int) + d982 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d257, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6125 p hg
    simpa only [d257, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d257, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6129 p hg
    simpa only [d257, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6131 (p : Pattern) (guard : d917 p = 1) : d258 p ≤ (0 : Int) + d983 p := by
  cases selected : p 108 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d258, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6112 p hg
    simpa only [d258, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d258, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6130 p hg
    simpa only [d258, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6132 (p : Pattern) (guard : d8 p = 1) : d57 p ≤ (1 : Int) + d57 p := by
  omega
theorem compare6133 (p : Pattern) (guard : d8 p = 1) : d7 p ≤ (1 : Int) + d7 p := by
  omega
theorem compare6134 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (1 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6135 (p : Pattern) (guard : d8 p = 1) : d8 p ≤ (1 : Int) + d0 p := by
  cases selected : p 271 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6134 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1006 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6136 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6137 (p : Pattern) (guard : d8 p = 1) : d9 p ≤ (1 : Int) + d2 p := by
  cases selected : p 271 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6136 p hg
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1009 p hg
    simpa only [d8, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6138 (p : Pattern) (guard : d8 p = 1) : d10 p ≤ (1 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6135 p hg
    simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6137 p hg
    simpa only [d10, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6139 (p : Pattern) (guard : d8 p = 1) : d11 p ≤ (1 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6135 p hg
    simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6138 p hg
    simpa only [d11, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6140 (p : Pattern) (guard : d8 p = 1) : d12 p ≤ (1 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6133 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6139 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6141 (p : Pattern) (guard : d8 p = 1) : d56 p ≤ (1 : Int) + d56 p := by
  omega
theorem compare6142 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (1 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6143 (p : Pattern) (guard : d8 p = 1) : d58 p ≤ (1 : Int) + d4 p := by
  cases selected : p 271 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d8, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6142 p hg
    simpa only [d8, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1016 p hg
    simpa only [d8, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6144 (p : Pattern) (guard : d8 p = 1) : d59 p ≤ (1 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6137 p hg
    simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6143 p hg
    simpa only [d59, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6145 (p : Pattern) (guard : d8 p = 1) : d60 p ≤ (1 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6137 p hg
    simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6144 p hg
    simpa only [d60, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6146 (p : Pattern) (guard : d8 p = 1) : d61 p ≤ (1 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6139 p hg
    simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6145 p hg
    simpa only [d61, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6147 (p : Pattern) (guard : d8 p = 1) : d62 p ≤ (1 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6141 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6146 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6148 (p : Pattern) (guard : d8 p = 1) : d63 p ≤ (1 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6140 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6147 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6149 (p : Pattern) (guard : d8 p = 1) : d64 p ≤ (1 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6132 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6150 (p : Pattern) (guard : d8 p = 1) : d179 p ≤ (1 : Int) + d179 p := by
  omega
theorem compare6151 (p : Pattern) (guard : d8 p = 1) : d55 p ≤ (1 : Int) + d55 p := by
  omega
theorem compare6152 (p : Pattern) (guard : d8 p = 1) : d65 p ≤ (1 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6151 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6145 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6153 (p : Pattern) (guard : d8 p = 1) : d109 p ≤ (1 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6140 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6154 (p : Pattern) (guard : d8 p = 1) : d120 p ≤ (1 : Int) + d120 p := by
  omega
theorem compare6155 (p : Pattern) (guard : d8 p = 1) : d125 p ≤ (1 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6139 p hg
    simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6145 p hg
    simpa only [d125, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6156 (p : Pattern) (guard : d8 p = 1) : d126 p ≤ (1 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6139 p hg
    simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6155 p hg
    simpa only [d126, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6157 (p : Pattern) (guard : d8 p = 1) : d127 p ≤ (1 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6154 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6156 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6158 (p : Pattern) (guard : d8 p = 1) : d128 p ≤ (1 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6157 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6159 (p : Pattern) (guard : d8 p = 1) : d129 p ≤ (1 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d8 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6153 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6158 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
