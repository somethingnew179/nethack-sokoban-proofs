/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5040 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (3 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5019 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5035 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5041 (p : Pattern) (guard : d1365 p = 1) : d59 p ≤ (3 : Int) + d24 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5013 p hg
    simpa only [d1365, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5040 p hg
    simpa only [d1365, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5042 (p : Pattern) (guard : d1365 p = 1) : d60 p ≤ (3 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d60, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5034 p hg
    simpa only [d60, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d60, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5041 p hg
    simpa only [d60, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5043 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5044 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (3 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5025 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5043 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5045 (p : Pattern) (guard : d1365 p = 1) : d62 p ≤ (3 : Int) + d40 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5023 p hg
    simpa only [d1365, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5044 p hg
    simpa only [d1365, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5046 (p : Pattern) (guard : d1365 p = 1) : d63 p ≤ (3 : Int) + d1103 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d63, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5045 p hg
    simpa only [d63, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d63, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5037 p hg
    simpa only [d63, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5047 (p : Pattern) (guard : d1365 p = 1) : d64 p ≤ (3 : Int) + d1109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d64, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5042 p hg
    simpa only [d64, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d64, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5046 p hg
    simpa only [d64, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5048 (p : Pattern) (guard : d1365 p = 1) : d65 p ≤ (3 : Int) + d1110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d65, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5039 p hg
    simpa only [d65, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d65, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5047 p hg
    simpa only [d65, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5049 (p : Pattern) (guard : d1365 p = 1) : d66 p ≤ (3 : Int) + d1110 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5031 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5048 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5050 (p : Pattern) (guard : d1365 p = 1) : d67 p ≤ (3 : Int) + d1111 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d67, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d67, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d67, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5049 p hg
    simpa only [d67, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5051 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (3 : Int) + d40 p := by
  omega
theorem compare5052 (p : Pattern) (guard : d1088 p = 1) : d68 p ≤ (3 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5043 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5053 (p : Pattern) (guard : d1365 p = 1) : d69 p ≤ (3 : Int) + d40 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5026 p hg
    simpa only [d1365, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5052 p hg
    simpa only [d1365, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5054 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (3 : Int) + d24 p := by
  omega
theorem compare5055 (p : Pattern) (guard : d1088 p = 1) : d70 p ≤ (3 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5035 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5056 (p : Pattern) (guard : d1365 p = 1) : d71 p ≤ (3 : Int) + d24 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5008 p hg
    simpa only [d1365, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d1365, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5057 (p : Pattern) (guard : d1365 p = 1) : d72 p ≤ (3 : Int) + d1103 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5053 p hg
    simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d72, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5058 (p : Pattern) (guard : d1365 p = 1) : d73 p ≤ (3 : Int) + d1104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d73, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5059 (p : Pattern) (guard : d1365 p = 1) : d74 p ≤ (3 : Int) + d1105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4976 p hg
    simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d74, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5060 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (3 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5061 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (3 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5062 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (3 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5061 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5063 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (3 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5064 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (3 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5065 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (3 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5066 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (3 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5065 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5067 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5068 (p : Pattern) (guard : d1088 p = 1) : d68 p ≤ (3 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5066 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5069 (p : Pattern) (guard : d1365 p = 1) : d68 p ≤ (3 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5068 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5070 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (3 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5071 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (3 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5061 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5072 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (3 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5071 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5073 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (3 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5071 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5074 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (3 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5072 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5075 (p : Pattern) (guard : d1088 p = 1) : d70 p ≤ (3 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5074 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5076 (p : Pattern) (guard : d1365 p = 1) : d70 p ≤ (3 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5070 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5075 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5077 (p : Pattern) (guard : d1365 p = 1) : d75 p ≤ (3 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5076 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5078 (p : Pattern) (guard : d1365 p = 1) : d76 p ≤ (3 : Int) + d1366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d76, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d76, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d76, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d76, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5079 (p : Pattern) (guard : d1365 p = 1) : d77 p ≤ (3 : Int) + d1367 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d77, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4976 p hg
    simpa only [d77, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d77, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5078 p hg
    simpa only [d77, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5080 (p : Pattern) (guard : d1365 p = 1) : d78 p ≤ (3 : Int) + d1368 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d78, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5059 p hg
    simpa only [d78, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d78, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d78, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5081 (p : Pattern) (guard : d1365 p = 1) : d79 p ≤ (3 : Int) + d1112 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d79, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5011 p hg
    simpa only [d79, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d79, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d79, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5082 (p : Pattern) (guard : d1365 p = 1) : d80 p ≤ (3 : Int) + d1113 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d80, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5012 p hg
    simpa only [d80, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d80, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d80, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5083 (p : Pattern) (guard : d1365 p = 1) : d81 p ≤ (3 : Int) + d1112 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d81, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5038 p hg
    simpa only [d81, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d81, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d81, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5084 (p : Pattern) (guard : d1365 p = 1) : d82 p ≤ (3 : Int) + d1113 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d82, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5039 p hg
    simpa only [d82, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d82, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5083 p hg
    simpa only [d82, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5085 (p : Pattern) (guard : d1365 p = 1) : d83 p ≤ (3 : Int) + d1113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5082 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5086 (p : Pattern) (guard : d1365 p = 1) : d84 p ≤ (3 : Int) + d1369 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d84, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5080 p hg
    simpa only [d84, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d84, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d84, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5087 (p : Pattern) (guard : d1365 p = 1) : d85 p ≤ (3 : Int) + d1370 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d85, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d85, d1370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d85, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5086 p hg
    simpa only [d85, d1370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5088 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5089 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (3 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4966 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5088 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5090 (p : Pattern) (guard : d1365 p = 1) : d86 p ≤ (3 : Int) + d8 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d1365, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5089 p hg
    simpa only [d1365, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5091 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5092 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (3 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4971 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5093 (p : Pattern) (guard : d1365 p = 1) : d87 p ≤ (3 : Int) + d20 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d1365, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5092 p hg
    simpa only [d1365, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5094 (p : Pattern) (guard : d1365 p = 1) : d88 p ≤ (3 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d88, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d88, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d88, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d88, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5095 (p : Pattern) (guard : d1365 p = 1) : d89 p ≤ (3 : Int) + d1098 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d89, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d89, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d89, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5094 p hg
    simpa only [d89, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5096 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5097 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (3 : Int) + d33 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4978 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5098 (p : Pattern) (guard : d1365 p = 1) : d90 p ≤ (3 : Int) + d33 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d1365, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5097 p hg
    simpa only [d1365, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5099 (p : Pattern) (guard : d1365 p = 1) : d91 p ≤ (3 : Int) + d1099 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d91, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d91, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d91, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5098 p hg
    simpa only [d91, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5100 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5101 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (3 : Int) + d38 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4984 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5100 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5102 (p : Pattern) (guard : d1365 p = 1) : d92 p ≤ (3 : Int) + d38 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d1365, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5101 p hg
    simpa only [d1365, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5103 (p : Pattern) (guard : d1365 p = 1) : d93 p ≤ (3 : Int) + d1100 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d93, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5102 p hg
    simpa only [d93, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d93, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d93, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5104 (p : Pattern) (guard : d1365 p = 1) : d94 p ≤ (3 : Int) + d1101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d94, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5099 p hg
    simpa only [d94, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d94, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5103 p hg
    simpa only [d94, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5105 (p : Pattern) (guard : d1365 p = 1) : d95 p ≤ (3 : Int) + d1102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d95, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5095 p hg
    simpa only [d95, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d95, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5104 p hg
    simpa only [d95, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5106 (p : Pattern) (guard : d1365 p = 1) : d96 p ≤ (3 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5107 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (3 : Int) + d14 p := by
  omega
theorem compare5108 (p : Pattern) (guard : d1088 p = 1) : d97 p ≤ (3 : Int) + d14 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5107 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5032 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5109 (p : Pattern) (guard : d1365 p = 1) : d98 p ≤ (3 : Int) + d14 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5000 p hg
    simpa only [d1365, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5108 p hg
    simpa only [d1365, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5110 (p : Pattern) (guard : d1365 p = 1) : d99 p ≤ (3 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5109 p hg
    simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d99, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5111 (p : Pattern) (guard : d1365 p = 1) : d100 p ≤ (3 : Int) + d1108 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5109 p hg
    simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d100, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5112 (p : Pattern) (guard : d1365 p = 1) : d101 p ≤ (3 : Int) + d1109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d101, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5113 (p : Pattern) (guard : d1365 p = 1) : d102 p ≤ (3 : Int) + d1110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5111 p hg
    simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5112 p hg
    simpa only [d102, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5114 (p : Pattern) (guard : d1365 p = 1) : d103 p ≤ (3 : Int) + d1111 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5106 p hg
    simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5113 p hg
    simpa only [d103, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5115 (p : Pattern) (guard : d1365 p = 1) : d104 p ≤ (3 : Int) + d1366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d104, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5094 p hg
    simpa only [d104, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d104, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d104, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5116 (p : Pattern) (guard : d1365 p = 1) : d105 p ≤ (3 : Int) + d1367 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d105, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5095 p hg
    simpa only [d105, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d105, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5115 p hg
    simpa only [d105, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5117 (p : Pattern) (guard : d1365 p = 1) : d106 p ≤ (3 : Int) + d1367 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5116 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5118 (p : Pattern) (guard : d1365 p = 1) : d2 p ≤ (3 : Int) + d2 p := by
  omega
theorem compare5119 (p : Pattern) (guard : d1365 p = 1) : d107 p ≤ (3 : Int) + d1112 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d107, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5120 (p : Pattern) (guard : d1365 p = 1) : d108 p ≤ (3 : Int) + d1113 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5111 p hg
    simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d108, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5121 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (3 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5122 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (3 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5123 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (3 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5122 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5124 (p : Pattern) (guard : d1088 p = 1) : d97 p ≤ (3 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5125 (p : Pattern) (guard : d1365 p = 1) : d97 p ≤ (3 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5121 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5124 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5126 (p : Pattern) (guard : d1365 p = 1) : d109 p ≤ (3 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5125 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5076 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5127 (p : Pattern) (guard : d1365 p = 1) : d110 p ≤ (3 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5125 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5128 (p : Pattern) (guard : d1365 p = 1) : d111 p ≤ (3 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5129 (p : Pattern) (guard : d1365 p = 1) : d112 p ≤ (3 : Int) + d2 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5127 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5128 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5130 (p : Pattern) (guard : d1365 p = 1) : d113 p ≤ (3 : Int) + d1117 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d113, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5120 p hg
    simpa only [d113, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d113, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5129 p hg
    simpa only [d113, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5131 (p : Pattern) (guard : d1365 p = 1) : d114 p ≤ (3 : Int) + d1371 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d114, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5117 p hg
    simpa only [d114, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d114, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5130 p hg
    simpa only [d114, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5132 (p : Pattern) (guard : d1365 p = 1) : d115 p ≤ (3 : Int) + d1372 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d115, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d115, d1372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d115, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5131 p hg
    simpa only [d115, d1372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5133 (p : Pattern) (guard : d1365 p = 1) : d116 p ≤ (3 : Int) + d1373 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d116, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5087 p hg
    simpa only [d116, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d116, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5132 p hg
    simpa only [d116, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5134 (p : Pattern) (guard : d1365 p = 1) : d117 p ≤ (3 : Int) + d1374 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d117, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d117, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d117, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d117, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5135 (p : Pattern) (guard : d1365 p = 1) : d118 p ≤ (3 : Int) + d1375 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d118, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d118, d1375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d118, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5134 p hg
    simpa only [d118, d1375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5136 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (3 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5137 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (3 : Int) + d4 p := by
  omega
theorem compare5138 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (3 : Int) + d0 p := by
  omega
theorem compare5139 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (3 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5140 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (3 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5139 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5141 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (3 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5137 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5142 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (3 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5143 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (3 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5141 p hg
    simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5142 p hg
    simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5144 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (3 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5143 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5145 (p : Pattern) (guard : d1365 p = 1) : d120 p ≤ (3 : Int) + d20 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5136 p hg
    simpa only [d1365, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5144 p hg
    simpa only [d1365, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5146 (p : Pattern) (guard : d1365 p = 1) : d121 p ≤ (3 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d121, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d121, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d121, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5145 p hg
    simpa only [d121, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5147 (p : Pattern) (guard : d1365 p = 1) : d122 p ≤ (3 : Int) + d1376 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d122, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5146 p hg
    simpa only [d122, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d122, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5103 p hg
    simpa only [d122, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5148 (p : Pattern) (guard : d1365 p = 1) : d123 p ≤ (3 : Int) + d1377 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d123, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5095 p hg
    simpa only [d123, d1377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d123, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5147 p hg
    simpa only [d123, d1377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5149 (p : Pattern) (guard : d1365 p = 1) : d124 p ≤ (3 : Int) + d1378 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d124, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d124, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d124, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d124, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5150 (p : Pattern) (guard : d1365 p = 1) : d125 p ≤ (3 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5151 (p : Pattern) (guard : d1365 p = 1) : d126 p ≤ (3 : Int) + d2 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5127 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5150 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5152 (p : Pattern) (guard : d1365 p = 1) : d127 p ≤ (3 : Int) + d1379 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d127, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5113 p hg
    simpa only [d127, d1379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d127, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5151 p hg
    simpa only [d127, d1379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5153 (p : Pattern) (guard : d1365 p = 1) : d128 p ≤ (3 : Int) + d1380 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d128, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5149 p hg
    simpa only [d128, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d128, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5152 p hg
    simpa only [d128, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5154 (p : Pattern) (guard : d1365 p = 1) : d129 p ≤ (3 : Int) + d1381 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d129, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d129, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d129, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d129, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5155 (p : Pattern) (guard : d1365 p = 1) : d130 p ≤ (3 : Int) + d2 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5129 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5156 (p : Pattern) (guard : d1365 p = 1) : d131 p ≤ (3 : Int) + d1382 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d131, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5154 p hg
    simpa only [d131, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d131, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5155 p hg
    simpa only [d131, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5157 (p : Pattern) (guard : d1365 p = 1) : d132 p ≤ (3 : Int) + d1383 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d132, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5153 p hg
    simpa only [d132, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d132, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5156 p hg
    simpa only [d132, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5158 (p : Pattern) (guard : d1365 p = 1) : d133 p ≤ (3 : Int) + d1384 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d133, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5135 p hg
    simpa only [d133, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d133, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5157 p hg
    simpa only [d133, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5159 (p : Pattern) (guard : d1365 p = 1) : d134 p ≤ (3 : Int) + d1385 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d134, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5133 p hg
    simpa only [d134, d1385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d134, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5158 p hg
    simpa only [d134, d1385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5160 (p : Pattern) (guard : d1072 p = 1) : d67 p ≤ (0 : Int) + d184 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d1072, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare419 p hg
    simpa only [d1072, d67, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5161 (p : Pattern) (guard : d1072 p = 1) : d84 p ≤ (0 : Int) + d185 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1743 p hg
    simpa only [d1072, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare422 p hg
    simpa only [d1072, d84, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5162 (p : Pattern) (guard : d1072 p = 1) : d85 p ≤ (0 : Int) + d186 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1072 p = 1 := by simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5160 p hg
    simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1072 p = 1 := by simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5161 p hg
    simpa only [d85, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5163 (p : Pattern) (guard : d0 p = 1) : d52 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5164 (p : Pattern) (guard : d857 p = 1) : d86 p ≤ (0 : Int) + d187 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d86, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d86, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d86, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d857, d86, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5165 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (0 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5166 (p : Pattern) (guard : d857 p = 1) : d87 p ≤ (0 : Int) + d188 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d87, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d87, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d87, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d857, d87, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5167 (p : Pattern) (guard : d857 p = 1) : d88 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d88, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d88, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d88, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d88, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5168 (p : Pattern) (guard : d857 p = 1) : d89 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d89, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d89, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d89, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5167 p hg
    simpa only [d89, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5169 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5170 (p : Pattern) (guard : d857 p = 1) : d90 p ≤ (0 : Int) + d191 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d90, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d90, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d90, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d857, d90, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5171 (p : Pattern) (guard : d857 p = 1) : d91 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d91, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d91, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d91, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5170 p hg
    simpa only [d91, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5172 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (0 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5173 (p : Pattern) (guard : d857 p = 1) : d92 p ≤ (0 : Int) + d193 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d92, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d92, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d92, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5172 p hg
    simpa only [d857, d92, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5174 (p : Pattern) (guard : d857 p = 1) : d93 p ≤ (0 : Int) + d194 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d93, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d93, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d93, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d93, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5175 (p : Pattern) (guard : d857 p = 1) : d94 p ≤ (0 : Int) + d195 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d94, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d94, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d94, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5174 p hg
    simpa only [d94, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5176 (p : Pattern) (guard : d857 p = 1) : d95 p ≤ (0 : Int) + d196 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d95, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5168 p hg
    simpa only [d95, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d95, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5175 p hg
    simpa only [d95, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5177 (p : Pattern) (guard : d857 p = 1) : d96 p ≤ (0 : Int) + d197 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d96, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d96, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d96, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5176 p hg
    simpa only [d96, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5178 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5179 (p : Pattern) (guard : d1072 p = 1) : d103 p ≤ (0 : Int) + d198 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1072, d103, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5177 p hg
    simpa only [d1072, d103, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1072, d103, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5178 p hg
    simpa only [d1072, d103, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
