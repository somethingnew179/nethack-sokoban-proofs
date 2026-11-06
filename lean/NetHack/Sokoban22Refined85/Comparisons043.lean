/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6020 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (2 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d59, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6021 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6020 p hg
    simpa only [d60, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6022 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (2 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6016 p hg
    simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d61, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6023 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (2 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6024 (p : Pattern) (guard : d4395 p = 1) : d64 p ≤ (2 : Int) + d55 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6022 p hg
    simpa only [d4395, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6023 p hg
    simpa only [d4395, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6025 (p : Pattern) (guard : d4617 p = 1) : d65 p ≤ (2 : Int) + d55 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6015 p hg
    simpa only [d4617, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6024 p hg
    simpa only [d4617, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6026 (p : Pattern) (guard : d0 p = 1) : d391 p ≤ (2 : Int) + d798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6027 (p : Pattern) (guard : d4618 p = 1) : d711 p ≤ (2 : Int) + d4620 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d711, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d4618, d711, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d711, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6026 p hg
    simpa only [d4618, d711, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6028 (p : Pattern) (guard : d4618 p = 1) : d712 p ≤ (2 : Int) + d4621 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d712, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6014 p hg
    simpa only [d712, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d712, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6027 p hg
    simpa only [d712, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6029 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6030 (p : Pattern) (guard : d4618 p = 1) : d713 p ≤ (2 : Int) + d4619 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d713, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d4618, d713, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d713, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6029 p hg
    simpa only [d4618, d713, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6031 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6032 (p : Pattern) (guard : d4618 p = 1) : d714 p ≤ (2 : Int) + d4622 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d714, d4622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d4618, d714, d4622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d714, d4622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d4618, d714, d4622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6033 (p : Pattern) (guard : d4618 p = 1) : d715 p ≤ (2 : Int) + d4623 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d715, d4623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6030 p hg
    simpa only [d715, d4623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d715, d4623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6032 p hg
    simpa only [d715, d4623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6034 (p : Pattern) (guard : d4618 p = 1) : d716 p ≤ (2 : Int) + d4624 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d716, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6028 p hg
    simpa only [d716, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d716, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d716, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6035 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6036 (p : Pattern) (guard : d4618 p = 1) : d717 p ≤ (2 : Int) + d4619 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d717, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d4618, d717, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d717, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6035 p hg
    simpa only [d4618, d717, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6037 (p : Pattern) (guard : d4618 p = 1) : d718 p ≤ (2 : Int) + d4623 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d718, d4623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6036 p hg
    simpa only [d718, d4623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d718, d4623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6032 p hg
    simpa only [d718, d4623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6038 (p : Pattern) (guard : d0 p = 1) : d90 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6039 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (2 : Int) + d63 p := by
  omega
theorem compare6040 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6041 (p : Pattern) (guard : d4395 p = 1) : d91 p ≤ (2 : Int) + d63 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6039 p hg
    simpa only [d4395, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6040 p hg
    simpa only [d4395, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6042 (p : Pattern) (guard : d4617 p = 1) : d92 p ≤ (2 : Int) + d63 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6038 p hg
    simpa only [d4617, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6041 p hg
    simpa only [d4617, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6043 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6044 (p : Pattern) (guard : d4618 p = 1) : d719 p ≤ (2 : Int) + d4625 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d719, d4625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6042 p hg
    simpa only [d4618, d719, d4625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d719, d4625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4618, d719, d4625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6045 (p : Pattern) (guard : d0 p = 1) : d91 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6046 (p : Pattern) (guard : d4395 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare6047 (p : Pattern) (guard : d4617 p = 1) : d93 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6045 p hg
    simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6046 p hg
    simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6048 (p : Pattern) (guard : d4618 p = 1) : d95 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6047 p hg
    simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6049 (p : Pattern) (guard : d4618 p = 1) : d720 p ≤ (2 : Int) + d4626 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d720, d4626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6044 p hg
    simpa only [d720, d4626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d720, d4626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6048 p hg
    simpa only [d720, d4626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6050 (p : Pattern) (guard : d4618 p = 1) : d721 p ≤ (2 : Int) + d4627 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d721, d4627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6037 p hg
    simpa only [d721, d4627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d721, d4627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d721, d4627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6051 (p : Pattern) (guard : d4618 p = 1) : d722 p ≤ (2 : Int) + d4628 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d722, d4628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6034 p hg
    simpa only [d722, d4628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d722, d4628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6050 p hg
    simpa only [d722, d4628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6052 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6053 (p : Pattern) (guard : d4618 p = 1) : d723 p ≤ (2 : Int) + d4619 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d723, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d4618, d723, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d723, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6052 p hg
    simpa only [d4618, d723, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6054 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (2 : Int) + d798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6055 (p : Pattern) (guard : d4618 p = 1) : d724 p ≤ (2 : Int) + d4620 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d724, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d4618, d724, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d724, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6054 p hg
    simpa only [d4618, d724, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6056 (p : Pattern) (guard : d4618 p = 1) : d725 p ≤ (2 : Int) + d4621 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d725, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6053 p hg
    simpa only [d725, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d725, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6055 p hg
    simpa only [d725, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6057 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6058 (p : Pattern) (guard : d4618 p = 1) : d726 p ≤ (2 : Int) + d4619 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d726, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d4618, d726, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d726, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6057 p hg
    simpa only [d4618, d726, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6059 (p : Pattern) (guard : d4618 p = 1) : d727 p ≤ (2 : Int) + d4623 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d727, d4623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d727, d4623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d727, d4623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6032 p hg
    simpa only [d727, d4623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6060 (p : Pattern) (guard : d4618 p = 1) : d728 p ≤ (2 : Int) + d4624 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d728, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6056 p hg
    simpa only [d728, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d728, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d728, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6061 (p : Pattern) (guard : d4618 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare6062 (p : Pattern) (guard : d4618 p = 1) : d729 p ≤ (2 : Int) + d4629 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d729, d4629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d729, d4629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d729, d4629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d729, d4629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6063 (p : Pattern) (guard : d4618 p = 1) : d730 p ≤ (2 : Int) + d4630 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d730, d4630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6060 p hg
    simpa only [d730, d4630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d730, d4630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6062 p hg
    simpa only [d730, d4630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6064 (p : Pattern) (guard : d4618 p = 1) : d731 p ≤ (2 : Int) + d4631 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d731, d4631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6051 p hg
    simpa only [d731, d4631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d731, d4631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6063 p hg
    simpa only [d731, d4631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6065 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6066 (p : Pattern) (guard : d4618 p = 1) : d732 p ≤ (2 : Int) + d4619 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d732, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d4618, d732, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d732, d4619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6065 p hg
    simpa only [d4618, d732, d4619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6067 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (2 : Int) + d798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6068 (p : Pattern) (guard : d4618 p = 1) : d733 p ≤ (2 : Int) + d4620 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d733, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d4618, d733, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d733, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6067 p hg
    simpa only [d4618, d733, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6069 (p : Pattern) (guard : d4618 p = 1) : d734 p ≤ (2 : Int) + d4621 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d734, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6066 p hg
    simpa only [d734, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d734, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6068 p hg
    simpa only [d734, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6070 (p : Pattern) (guard : d4618 p = 1) : d735 p ≤ (2 : Int) + d4624 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d735, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6069 p hg
    simpa only [d735, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d735, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d735, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6071 (p : Pattern) (guard : d4618 p = 1) : d736 p ≤ (2 : Int) + d4627 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d736, d4627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d736, d4627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d736, d4627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d736, d4627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6072 (p : Pattern) (guard : d4618 p = 1) : d737 p ≤ (2 : Int) + d4628 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d737, d4628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6070 p hg
    simpa only [d737, d4628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d737, d4628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6071 p hg
    simpa only [d737, d4628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6073 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6074 (p : Pattern) (guard : d4618 p = 1) : d714 p ≤ (2 : Int) + d4620 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d714, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d4618, d714, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d714, d4620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6073 p hg
    simpa only [d4618, d714, d4620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6075 (p : Pattern) (guard : d4618 p = 1) : d718 p ≤ (2 : Int) + d4621 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d718, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6036 p hg
    simpa only [d718, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d718, d4621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6074 p hg
    simpa only [d718, d4621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6076 (p : Pattern) (guard : d4618 p = 1) : d738 p ≤ (2 : Int) + d4624 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d738, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6075 p hg
    simpa only [d738, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d738, d4624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d738, d4624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6077 (p : Pattern) (guard : d4618 p = 1) : d739 p ≤ (2 : Int) + d4630 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d739, d4630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6076 p hg
    simpa only [d739, d4630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d739, d4630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6062 p hg
    simpa only [d739, d4630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6078 (p : Pattern) (guard : d4618 p = 1) : d740 p ≤ (2 : Int) + d4631 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d740, d4631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6072 p hg
    simpa only [d740, d4631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d740, d4631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6077 p hg
    simpa only [d740, d4631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6079 (p : Pattern) (guard : d4618 p = 1) : d741 p ≤ (2 : Int) + d4631 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6078 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6080 (p : Pattern) (guard : d0 p = 1) : d111 p ≤ (2 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6081 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (2 : Int) + d110 p := by
  omega
theorem compare6082 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (2 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6083 (p : Pattern) (guard : d4395 p = 1) : d113 p ≤ (2 : Int) + d110 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6081 p hg
    simpa only [d4395, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6082 p hg
    simpa only [d4395, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6084 (p : Pattern) (guard : d4617 p = 1) : d114 p ≤ (2 : Int) + d110 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6080 p hg
    simpa only [d4617, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6083 p hg
    simpa only [d4617, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6085 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (2 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6086 (p : Pattern) (guard : d4618 p = 1) : d742 p ≤ (2 : Int) + d4632 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d742, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d4618, d742, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d742, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6085 p hg
    simpa only [d4618, d742, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6087 (p : Pattern) (guard : d0 p = 1) : d135 p ≤ (2 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6088 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d10 p := by
  change (11 : Int) ≤ (2 : Int) + 10
  decide
theorem compare6089 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6088 p hg
    simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6090 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6088 p hg
    simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6091 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (2 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6090 p hg
    simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6092 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6090 p hg
    simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6091 p hg
    simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6093 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (2 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5517 p hg
    simpa only [d136, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6092 p hg
    simpa only [d136, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6094 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6095 (p : Pattern) (guard : d4395 p = 1) : d137 p ≤ (2 : Int) + d134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6093 p hg
    simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d4395, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6096 (p : Pattern) (guard : d4617 p = 1) : d138 p ≤ (2 : Int) + d134 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6087 p hg
    simpa only [d4617, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6095 p hg
    simpa only [d4617, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6097 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (2 : Int) + d863 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6098 (p : Pattern) (guard : d4618 p = 1) : d743 p ≤ (2 : Int) + d4633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d743, d4633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d4618, d743, d4633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d743, d4633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6097 p hg
    simpa only [d4618, d743, d4633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6099 (p : Pattern) (guard : d4618 p = 1) : d744 p ≤ (2 : Int) + d4634 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d744, d4634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6086 p hg
    simpa only [d744, d4634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d744, d4634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6098 p hg
    simpa only [d744, d4634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6100 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6101 (p : Pattern) (guard : d4618 p = 1) : d745 p ≤ (2 : Int) + d4632 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d745, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d4618, d745, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d745, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6100 p hg
    simpa only [d4618, d745, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6102 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6103 (p : Pattern) (guard : d4618 p = 1) : d746 p ≤ (2 : Int) + d4635 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d746, d4635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d4618, d746, d4635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d746, d4635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6102 p hg
    simpa only [d4618, d746, d4635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6104 (p : Pattern) (guard : d4618 p = 1) : d747 p ≤ (2 : Int) + d4636 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d747, d4636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6101 p hg
    simpa only [d747, d4636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d747, d4636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6103 p hg
    simpa only [d747, d4636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6105 (p : Pattern) (guard : d4618 p = 1) : d748 p ≤ (2 : Int) + d4637 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d748, d4637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6099 p hg
    simpa only [d748, d4637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d748, d4637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6104 p hg
    simpa only [d748, d4637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6106 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (2 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6107 (p : Pattern) (guard : d4618 p = 1) : d749 p ≤ (2 : Int) + d4632 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d749, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d4618, d749, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d749, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6106 p hg
    simpa only [d4618, d749, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6108 (p : Pattern) (guard : d4618 p = 1) : d750 p ≤ (2 : Int) + d4636 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d750, d4636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6107 p hg
    simpa only [d750, d4636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d750, d4636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6103 p hg
    simpa only [d750, d4636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6109 (p : Pattern) (guard : d0 p = 1) : d159 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6110 (p : Pattern) (guard : d4617 p = 1) : d160 p ≤ (2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6109 p hg
    simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6046 p hg
    simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6111 (p : Pattern) (guard : d4618 p = 1) : d161 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6112 (p : Pattern) (guard : d4618 p = 1) : d162 p ≤ (2 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6111 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6113 (p : Pattern) (guard : d4618 p = 1) : d751 p ≤ (2 : Int) + d4638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d751, d4638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6108 p hg
    simpa only [d751, d4638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d751, d4638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6112 p hg
    simpa only [d751, d4638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6114 (p : Pattern) (guard : d4618 p = 1) : d752 p ≤ (2 : Int) + d4639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d752, d4639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6105 p hg
    simpa only [d752, d4639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d752, d4639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6113 p hg
    simpa only [d752, d4639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6115 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (2 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6116 (p : Pattern) (guard : d4618 p = 1) : d753 p ≤ (2 : Int) + d4632 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d753, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d4618, d753, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d753, d4632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6115 p hg
    simpa only [d4618, d753, d4632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6117 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d863 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6118 (p : Pattern) (guard : d4618 p = 1) : d746 p ≤ (2 : Int) + d4633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d746, d4633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d4618, d746, d4633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d746, d4633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6117 p hg
    simpa only [d4618, d746, d4633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6119 (p : Pattern) (guard : d4618 p = 1) : d754 p ≤ (2 : Int) + d4634 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d754, d4634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6116 p hg
    simpa only [d754, d4634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d754, d4634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6118 p hg
    simpa only [d754, d4634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6120 (p : Pattern) (guard : d4618 p = 1) : d755 p ≤ (2 : Int) + d4637 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d755, d4637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6119 p hg
    simpa only [d755, d4637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d755, d4637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6104 p hg
    simpa only [d755, d4637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6121 (p : Pattern) (guard : d4618 p = 1) : d756 p ≤ (2 : Int) + d4638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d756, d4638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6104 p hg
    simpa only [d756, d4638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d756, d4638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d756, d4638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6122 (p : Pattern) (guard : d4618 p = 1) : d757 p ≤ (2 : Int) + d4639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d757, d4639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6120 p hg
    simpa only [d757, d4639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d757, d4639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6121 p hg
    simpa only [d757, d4639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6123 (p : Pattern) (guard : d4618 p = 1) : d758 p ≤ (2 : Int) + d4639 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6114 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6122 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6124 (p : Pattern) (guard : d4618 p = 1) : d759 p ≤ (2 : Int) + d4640 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d759, d4640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d759, d4640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d759, d4640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6123 p hg
    simpa only [d759, d4640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6125 (p : Pattern) (guard : d4618 p = 1) : d760 p ≤ (2 : Int) + d4641 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d760, d4641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6079 p hg
    simpa only [d760, d4641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d760, d4641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6124 p hg
    simpa only [d760, d4641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6126 (p : Pattern) (guard : d0 p = 1) : d188 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6127 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (2 : Int) + d79 p := by
  omega
theorem compare6128 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (2 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6129 (p : Pattern) (guard : d4395 p = 1) : d80 p ≤ (2 : Int) + d79 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6127 p hg
    simpa only [d4395, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6128 p hg
    simpa only [d4395, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6130 (p : Pattern) (guard : d4617 p = 1) : d189 p ≤ (2 : Int) + d79 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6126 p hg
    simpa only [d4617, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6129 p hg
    simpa only [d4617, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6131 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d194 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6132 (p : Pattern) (guard : d4618 p = 1) : d761 p ≤ (2 : Int) + d4642 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d761, d4642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6130 p hg
    simpa only [d4618, d761, d4642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d761, d4642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6131 p hg
    simpa only [d4618, d761, d4642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6133 (p : Pattern) (guard : d0 p = 1) : d199 p ≤ (2 : Int) + d198 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6134 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (2 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d83, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d83, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6135 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d198 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6136 (p : Pattern) (guard : d4395 p = 1) : d84 p ≤ (2 : Int) + d198 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6134 p hg
    simpa only [d4395, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6135 p hg
    simpa only [d4395, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6137 (p : Pattern) (guard : d4617 p = 1) : d200 p ≤ (2 : Int) + d198 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6133 p hg
    simpa only [d4617, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6136 p hg
    simpa only [d4617, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6138 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6139 (p : Pattern) (guard : d4618 p = 1) : d762 p ≤ (2 : Int) + d4643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d762, d4643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6137 p hg
    simpa only [d4618, d762, d4643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d762, d4643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6138 p hg
    simpa only [d4618, d762, d4643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6140 (p : Pattern) (guard : d4618 p = 1) : d763 p ≤ (2 : Int) + d4644 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d763, d4644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6132 p hg
    simpa only [d763, d4644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d763, d4644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6139 p hg
    simpa only [d763, d4644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6141 (p : Pattern) (guard : d4618 p = 1) : d764 p ≤ (2 : Int) + d4645 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d764, d4645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6075 p hg
    simpa only [d764, d4645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d764, d4645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6140 p hg
    simpa only [d764, d4645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6142 (p : Pattern) (guard : d4618 p = 1) : d765 p ≤ (2 : Int) + d4646 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d765, d4646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6140 p hg
    simpa only [d765, d4646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d765, d4646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d765, d4646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6143 (p : Pattern) (guard : d4618 p = 1) : d766 p ≤ (2 : Int) + d4647 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d766, d4647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6141 p hg
    simpa only [d766, d4647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d766, d4647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6142 p hg
    simpa only [d766, d4647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6144 (p : Pattern) (guard : d4618 p = 1) : d767 p ≤ (2 : Int) + d4648 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d767, d4648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6072 p hg
    simpa only [d767, d4648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d767, d4648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6143 p hg
    simpa only [d767, d4648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6145 (p : Pattern) (guard : d4618 p = 1) : d768 p ≤ (2 : Int) + d4649 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d768, d4649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d768, d4649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d768, d4649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6144 p hg
    simpa only [d768, d4649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6146 (p : Pattern) (guard : d0 p = 1) : d212 p ≤ (2 : Int) + d211 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6147 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (2 : Int) + d211 p := by
  omega
theorem compare6148 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d211 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6149 (p : Pattern) (guard : d4395 p = 1) : d213 p ≤ (2 : Int) + d211 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6147 p hg
    simpa only [d4395, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d4395, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6150 (p : Pattern) (guard : d4617 p = 1) : d214 p ≤ (2 : Int) + d211 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6146 p hg
    simpa only [d4617, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6149 p hg
    simpa only [d4617, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6151 (p : Pattern) (guard : d4618 p = 1) : d769 p ≤ (2 : Int) + d4650 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d769, d4650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6150 p hg
    simpa only [d4618, d769, d4650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d769, d4650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6097 p hg
    simpa only [d4618, d769, d4650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6152 (p : Pattern) (guard : d4618 p = 1) : d770 p ≤ (2 : Int) + d4651 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d770, d4651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6086 p hg
    simpa only [d770, d4651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d770, d4651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6151 p hg
    simpa only [d770, d4651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6153 (p : Pattern) (guard : d4618 p = 1) : d771 p ≤ (2 : Int) + d4652 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d771, d4652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6150 p hg
    simpa only [d4618, d771, d4652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d771, d4652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6102 p hg
    simpa only [d4618, d771, d4652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6154 (p : Pattern) (guard : d4618 p = 1) : d772 p ≤ (2 : Int) + d4653 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d772, d4653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6101 p hg
    simpa only [d772, d4653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d772, d4653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6153 p hg
    simpa only [d772, d4653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6155 (p : Pattern) (guard : d4618 p = 1) : d773 p ≤ (2 : Int) + d4654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d773, d4654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d773, d4654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d773, d4654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6154 p hg
    simpa only [d773, d4654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6156 (p : Pattern) (guard : d4618 p = 1) : d774 p ≤ (2 : Int) + d4653 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d774, d4653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6107 p hg
    simpa only [d774, d4653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d774, d4653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6153 p hg
    simpa only [d774, d4653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6157 (p : Pattern) (guard : d4618 p = 1) : d775 p ≤ (2 : Int) + d4655 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d775, d4655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6156 p hg
    simpa only [d775, d4655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d775, d4655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6112 p hg
    simpa only [d775, d4655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6158 (p : Pattern) (guard : d4618 p = 1) : d776 p ≤ (2 : Int) + d4656 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d776, d4656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6155 p hg
    simpa only [d776, d4656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d776, d4656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6157 p hg
    simpa only [d776, d4656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6159 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d300 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
