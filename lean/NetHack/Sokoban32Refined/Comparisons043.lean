/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6020 (p : Pattern) (guard : d1365 p = 1) : d58 p ≤ (0 : Int) + d34 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6021 (p : Pattern) (guard : d1365 p = 1) : d472 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6014 p hg
    simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6020 p hg
    simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6022 (p : Pattern) (guard : d1365 p = 1) : d61 p ≤ (0 : Int) + d41 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare447 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6023 (p : Pattern) (guard : d1365 p = 1) : d473 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6022 p hg
    simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6024 (p : Pattern) (guard : d1365 p = 1) : d474 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6021 p hg
    simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6023 p hg
    simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6025 (p : Pattern) (guard : d1365 p = 1) : d475 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6024 p hg
    simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6026 (p : Pattern) (guard : d1365 p = 1) : d476 p ≤ (0 : Int) + d1389 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d476, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d476, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d476, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d476, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6027 (p : Pattern) (guard : d1365 p = 1) : d477 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d477, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5995 p hg
    simpa only [d477, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d477, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d477, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6028 (p : Pattern) (guard : d0 p = 1) : d478 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6029 (p : Pattern) (guard : d1365 p = 1) : d479 p ≤ (0 : Int) + d40 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6028 p hg
    simpa only [d1365, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d1365, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6030 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6031 (p : Pattern) (guard : d1365 p = 1) : d70 p ≤ (0 : Int) + d24 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6030 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6032 (p : Pattern) (guard : d1365 p = 1) : d480 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d480, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6029 p hg
    simpa only [d480, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d480, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d480, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6033 (p : Pattern) (guard : d1365 p = 1) : d481 p ≤ (0 : Int) + d1104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d481, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6027 p hg
    simpa only [d481, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d481, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6032 p hg
    simpa only [d481, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6034 (p : Pattern) (guard : d1365 p = 1) : d482 p ≤ (0 : Int) + d1105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d482, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6004 p hg
    simpa only [d482, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d482, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6033 p hg
    simpa only [d482, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6035 (p : Pattern) (guard : d0 p = 1) : d483 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6036 (p : Pattern) (guard : d1365 p = 1) : d484 p ≤ (0 : Int) + d8 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6035 p hg
    simpa only [d1365, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d1365, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6037 (p : Pattern) (guard : d1365 p = 1) : d485 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d485, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6036 p hg
    simpa only [d485, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d485, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d485, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6038 (p : Pattern) (guard : d1365 p = 1) : d75 p ≤ (0 : Int) + d75 p := by
  omega
theorem compare6039 (p : Pattern) (guard : d1365 p = 1) : d486 p ≤ (0 : Int) + d1390 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d486, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6037 p hg
    simpa only [d486, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d486, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6038 p hg
    simpa only [d486, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6040 (p : Pattern) (guard : d1365 p = 1) : d487 p ≤ (0 : Int) + d1391 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d487, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6004 p hg
    simpa only [d487, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d487, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6039 p hg
    simpa only [d487, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6041 (p : Pattern) (guard : d1365 p = 1) : d488 p ≤ (0 : Int) + d1392 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d488, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6034 p hg
    simpa only [d488, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d488, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6040 p hg
    simpa only [d488, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6042 (p : Pattern) (guard : d1365 p = 1) : d461 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6014 p hg
    simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6043 (p : Pattern) (guard : d1365 p = 1) : d489 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6042 p hg
    simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6038 p hg
    simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6044 (p : Pattern) (guard : d1365 p = 1) : d490 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6045 (p : Pattern) (guard : d1365 p = 1) : d491 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6018 p hg
    simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6038 p hg
    simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6046 (p : Pattern) (guard : d1365 p = 1) : d492 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6045 p hg
    simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6047 (p : Pattern) (guard : d1365 p = 1) : d493 p ≤ (0 : Int) + d80 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6044 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6046 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6048 (p : Pattern) (guard : d1365 p = 1) : d494 p ≤ (0 : Int) + d1393 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d494, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6041 p hg
    simpa only [d494, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d494, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6047 p hg
    simpa only [d494, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6049 (p : Pattern) (guard : d1365 p = 1) : d495 p ≤ (0 : Int) + d1394 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d495, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6026 p hg
    simpa only [d495, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d495, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6048 p hg
    simpa only [d495, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6050 (p : Pattern) (guard : d1365 p = 1) : d496 p ≤ (0 : Int) + d1099 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d496, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6036 p hg
    simpa only [d496, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d496, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6006 p hg
    simpa only [d496, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6051 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (0 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6052 (p : Pattern) (guard : d1365 p = 1) : d61 p ≤ (0 : Int) + d38 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6051 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6053 (p : Pattern) (guard : d1365 p = 1) : d473 p ≤ (0 : Int) + d1100 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d473, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6052 p hg
    simpa only [d473, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d473, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d473, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6054 (p : Pattern) (guard : d1365 p = 1) : d497 p ≤ (0 : Int) + d1101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d497, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6050 p hg
    simpa only [d497, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d497, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6053 p hg
    simpa only [d497, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6055 (p : Pattern) (guard : d1365 p = 1) : d498 p ≤ (0 : Int) + d1102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d498, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6004 p hg
    simpa only [d498, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d498, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6054 p hg
    simpa only [d498, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6056 (p : Pattern) (guard : d1365 p = 1) : d499 p ≤ (0 : Int) + d1102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6012 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6055 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6057 (p : Pattern) (guard : d0 p = 1) : d500 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6058 (p : Pattern) (guard : d1365 p = 1) : d501 p ≤ (0 : Int) + d14 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6057 p hg
    simpa only [d1365, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d1365, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6059 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6060 (p : Pattern) (guard : d1365 p = 1) : d97 p ≤ (0 : Int) + d14 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6059 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6061 (p : Pattern) (guard : d1365 p = 1) : d502 p ≤ (0 : Int) + d14 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6060 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6062 (p : Pattern) (guard : d1365 p = 1) : d109 p ≤ (0 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6060 p hg
    simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d109, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6063 (p : Pattern) (guard : d1365 p = 1) : d503 p ≤ (0 : Int) + d1108 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d503, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6061 p hg
    simpa only [d503, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d503, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6062 p hg
    simpa only [d503, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6064 (p : Pattern) (guard : d1365 p = 1) : d504 p ≤ (0 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d504, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d504, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d504, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d504, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6065 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6066 (p : Pattern) (guard : d1365 p = 1) : d68 p ≤ (0 : Int) + d40 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6065 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6067 (p : Pattern) (guard : d1365 p = 1) : d75 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6066 p hg
    simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6031 p hg
    simpa only [d75, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6068 (p : Pattern) (guard : d1365 p = 1) : d505 p ≤ (0 : Int) + d1109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d505, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d505, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d505, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6067 p hg
    simpa only [d505, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6069 (p : Pattern) (guard : d1365 p = 1) : d506 p ≤ (0 : Int) + d1110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d506, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6063 p hg
    simpa only [d506, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d506, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6068 p hg
    simpa only [d506, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6070 (p : Pattern) (guard : d1365 p = 1) : d125 p ≤ (0 : Int) + d1109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d125, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6062 p hg
    simpa only [d125, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d125, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6067 p hg
    simpa only [d125, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6071 (p : Pattern) (guard : d1365 p = 1) : d507 p ≤ (0 : Int) + d1110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d507, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6063 p hg
    simpa only [d507, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d507, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6070 p hg
    simpa only [d507, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6072 (p : Pattern) (guard : d1365 p = 1) : d508 p ≤ (0 : Int) + d1110 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6069 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6071 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6073 (p : Pattern) (guard : d1365 p = 1) : d509 p ≤ (0 : Int) + d1111 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d509, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6056 p hg
    simpa only [d509, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d509, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6072 p hg
    simpa only [d509, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6074 (p : Pattern) (guard : d1365 p = 1) : d510 p ≤ (0 : Int) + d8 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6036 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5997 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6075 (p : Pattern) (guard : d1365 p = 1) : d470 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d470, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5997 p hg
    simpa only [d470, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d470, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d470, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6076 (p : Pattern) (guard : d1365 p = 1) : d511 p ≤ (0 : Int) + d1098 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d511, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6074 p hg
    simpa only [d511, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d511, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6075 p hg
    simpa only [d511, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6077 (p : Pattern) (guard : d1365 p = 1) : d491 p ≤ (0 : Int) + d1390 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d491, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6075 p hg
    simpa only [d491, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d491, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6038 p hg
    simpa only [d491, d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6078 (p : Pattern) (guard : d1365 p = 1) : d512 p ≤ (0 : Int) + d1391 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d512, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6076 p hg
    simpa only [d512, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d512, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6077 p hg
    simpa only [d512, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6079 (p : Pattern) (guard : d1365 p = 1) : d513 p ≤ (0 : Int) + d1391 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6040 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6078 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6080 (p : Pattern) (guard : d1365 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare6081 (p : Pattern) (guard : d1365 p = 1) : d111 p ≤ (0 : Int) + d1112 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6062 p hg
    simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6080 p hg
    simpa only [d111, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6082 (p : Pattern) (guard : d1365 p = 1) : d514 p ≤ (0 : Int) + d1113 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d514, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6063 p hg
    simpa only [d514, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d514, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6081 p hg
    simpa only [d514, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6083 (p : Pattern) (guard : d1365 p = 1) : d112 p ≤ (0 : Int) + d112 p := by
  omega
theorem compare6084 (p : Pattern) (guard : d1365 p = 1) : d515 p ≤ (0 : Int) + d1395 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d515, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6082 p hg
    simpa only [d515, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d515, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6083 p hg
    simpa only [d515, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6085 (p : Pattern) (guard : d1365 p = 1) : d516 p ≤ (0 : Int) + d1396 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d516, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6079 p hg
    simpa only [d516, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d516, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6084 p hg
    simpa only [d516, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6086 (p : Pattern) (guard : d1365 p = 1) : d517 p ≤ (0 : Int) + d1397 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d517, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6073 p hg
    simpa only [d517, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d517, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6085 p hg
    simpa only [d517, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6087 (p : Pattern) (guard : d1365 p = 1) : d518 p ≤ (0 : Int) + d1398 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d518, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6049 p hg
    simpa only [d518, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d518, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6086 p hg
    simpa only [d518, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6088 (p : Pattern) (guard : d1365 p = 1) : d519 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d519, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6015 p hg
    simpa only [d519, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d519, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6020 p hg
    simpa only [d519, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6089 (p : Pattern) (guard : d1365 p = 1) : d520 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d520, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6088 p hg
    simpa only [d520, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d520, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6023 p hg
    simpa only [d520, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6090 (p : Pattern) (guard : d1365 p = 1) : d521 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d521, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6019 p hg
    simpa only [d521, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d521, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d521, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6091 (p : Pattern) (guard : d1365 p = 1) : d522 p ≤ (0 : Int) + d51 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6025 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6090 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6092 (p : Pattern) (guard : d1365 p = 1) : d523 p ≤ (0 : Int) + d1389 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d523, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6056 p hg
    simpa only [d523, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d523, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6091 p hg
    simpa only [d523, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6093 (p : Pattern) (guard : d1365 p = 1) : d524 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d524, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6015 p hg
    simpa only [d524, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d524, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6018 p hg
    simpa only [d524, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6094 (p : Pattern) (guard : d1365 p = 1) : d525 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d525, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6093 p hg
    simpa only [d525, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d525, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6045 p hg
    simpa only [d525, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6095 (p : Pattern) (guard : d1365 p = 1) : d526 p ≤ (0 : Int) + d80 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6046 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6096 (p : Pattern) (guard : d1365 p = 1) : d527 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d527, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6079 p hg
    simpa only [d527, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d527, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6095 p hg
    simpa only [d527, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6097 (p : Pattern) (guard : d1365 p = 1) : d528 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d528, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6092 p hg
    simpa only [d528, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d528, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6096 p hg
    simpa only [d528, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6098 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6099 (p : Pattern) (guard : d1365 p = 1) : d58 p ≤ (0 : Int) + d119 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6098 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6100 (p : Pattern) (guard : d1365 p = 1) : d519 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d519, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5997 p hg
    simpa only [d519, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d519, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6099 p hg
    simpa only [d519, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6101 (p : Pattern) (guard : d1365 p = 1) : d520 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d520, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6100 p hg
    simpa only [d520, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d520, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6053 p hg
    simpa only [d520, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6102 (p : Pattern) (guard : d1365 p = 1) : d529 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d529, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6076 p hg
    simpa only [d529, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d529, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6101 p hg
    simpa only [d529, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6103 (p : Pattern) (guard : d1365 p = 1) : d530 p ≤ (0 : Int) + d1404 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d530, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6055 p hg
    simpa only [d530, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d530, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6102 p hg
    simpa only [d530, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6104 (p : Pattern) (guard : d1365 p = 1) : d126 p ≤ (0 : Int) + d126 p := by
  omega
theorem compare6105 (p : Pattern) (guard : d1365 p = 1) : d531 p ≤ (0 : Int) + d1405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d531, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6071 p hg
    simpa only [d531, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d531, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6104 p hg
    simpa only [d531, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6106 (p : Pattern) (guard : d1365 p = 1) : d532 p ≤ (0 : Int) + d1406 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d532, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6103 p hg
    simpa only [d532, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d532, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6105 p hg
    simpa only [d532, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6107 (p : Pattern) (guard : d1365 p = 1) : d533 p ≤ (0 : Int) + d1407 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d533, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6078 p hg
    simpa only [d533, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d533, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6094 p hg
    simpa only [d533, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6108 (p : Pattern) (guard : d1365 p = 1) : d130 p ≤ (0 : Int) + d130 p := by
  omega
theorem compare6109 (p : Pattern) (guard : d1365 p = 1) : d534 p ≤ (0 : Int) + d1408 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d534, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6107 p hg
    simpa only [d534, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d534, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6108 p hg
    simpa only [d534, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6110 (p : Pattern) (guard : d1365 p = 1) : d535 p ≤ (0 : Int) + d1409 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d535, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6106 p hg
    simpa only [d535, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d535, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6109 p hg
    simpa only [d535, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6111 (p : Pattern) (guard : d1365 p = 1) : d536 p ≤ (0 : Int) + d1410 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d536, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6097 p hg
    simpa only [d536, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d536, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6110 p hg
    simpa only [d536, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6112 (p : Pattern) (guard : d1365 p = 1) : d537 p ≤ (0 : Int) + d1411 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d537, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6087 p hg
    simpa only [d537, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d537, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6111 p hg
    simpa only [d537, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6113 (p : Pattern) (guard : d0 p = 1) : d468 p ≤ (0 : Int) + d45 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6114 (p : Pattern) (guard : d1095 p = 1) : d468 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6113 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6115 (p : Pattern) (guard : d0 p = 1) : d475 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6116 (p : Pattern) (guard : d1095 p = 1) : d475 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6115 p hg
    simpa only [d1095, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6117 (p : Pattern) (guard : d1095 p = 1) : d476 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6114 p hg
    simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6116 p hg
    simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6118 (p : Pattern) (guard : d0 p = 1) : d487 p ≤ (0 : Int) + d77 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6119 (p : Pattern) (guard : d1095 p = 1) : d488 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d1095, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6118 p hg
    simpa only [d1095, d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6120 (p : Pattern) (guard : d0 p = 1) : d492 p ≤ (0 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6121 (p : Pattern) (guard : d1095 p = 1) : d493 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5743 p hg
    simpa only [d1095, d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6120 p hg
    simpa only [d1095, d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6122 (p : Pattern) (guard : d1095 p = 1) : d494 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6119 p hg
    simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6121 p hg
    simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6123 (p : Pattern) (guard : d1095 p = 1) : d495 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6117 p hg
    simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6122 p hg
    simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6124 (p : Pattern) (guard : d0 p = 1) : d498 p ≤ (0 : Int) + d95 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6125 (p : Pattern) (guard : d1095 p = 1) : d499 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1095, d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6124 p hg
    simpa only [d1095, d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6126 (p : Pattern) (guard : d0 p = 1) : d507 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6127 (p : Pattern) (guard : d1095 p = 1) : d508 p ≤ (0 : Int) + d102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6126 p hg
    simpa only [d1095, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6128 (p : Pattern) (guard : d1095 p = 1) : d509 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6125 p hg
    simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6127 p hg
    simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6129 (p : Pattern) (guard : d0 p = 1) : d512 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6130 (p : Pattern) (guard : d1095 p = 1) : d513 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d1095, d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6129 p hg
    simpa only [d1095, d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6131 (p : Pattern) (guard : d1095 p = 1) : d515 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5775 p hg
    simpa only [d1095, d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2227 p hg
    simpa only [d1095, d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6132 (p : Pattern) (guard : d1095 p = 1) : d516 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6130 p hg
    simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6131 p hg
    simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6133 (p : Pattern) (guard : d1095 p = 1) : d517 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6128 p hg
    simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6132 p hg
    simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6134 (p : Pattern) (guard : d1095 p = 1) : d518 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6123 p hg
    simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6133 p hg
    simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6135 (p : Pattern) (guard : d0 p = 1) : d498 p ≤ (0 : Int) + d45 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6136 (p : Pattern) (guard : d1095 p = 1) : d499 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6135 p hg
    simpa only [d1095, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6137 (p : Pattern) (guard : d0 p = 1) : d521 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6138 (p : Pattern) (guard : d1095 p = 1) : d522 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d1095, d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6137 p hg
    simpa only [d1095, d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6139 (p : Pattern) (guard : d1095 p = 1) : d523 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6136 p hg
    simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6138 p hg
    simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6140 (p : Pattern) (guard : d0 p = 1) : d512 p ≤ (0 : Int) + d77 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6141 (p : Pattern) (guard : d1095 p = 1) : d513 p ≤ (0 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6140 p hg
    simpa only [d1095, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6142 (p : Pattern) (guard : d0 p = 1) : d525 p ≤ (0 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6143 (p : Pattern) (guard : d1095 p = 1) : d526 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5784 p hg
    simpa only [d1095, d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6142 p hg
    simpa only [d1095, d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6144 (p : Pattern) (guard : d1095 p = 1) : d527 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6141 p hg
    simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6143 p hg
    simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6145 (p : Pattern) (guard : d1095 p = 1) : d528 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6139 p hg
    simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6144 p hg
    simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6146 (p : Pattern) (guard : d0 p = 1) : d529 p ≤ (0 : Int) + d123 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6147 (p : Pattern) (guard : d1095 p = 1) : d530 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d1095, d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6146 p hg
    simpa only [d1095, d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6148 (p : Pattern) (guard : d1095 p = 1) : d531 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d1095, d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2245 p hg
    simpa only [d1095, d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6149 (p : Pattern) (guard : d1095 p = 1) : d532 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6147 p hg
    simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6148 p hg
    simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6150 (p : Pattern) (guard : d1095 p = 1) : d533 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d1095, d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6142 p hg
    simpa only [d1095, d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6151 (p : Pattern) (guard : d1095 p = 1) : d534 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6150 p hg
    simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1862 p hg
    simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6152 (p : Pattern) (guard : d1095 p = 1) : d535 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6149 p hg
    simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6151 p hg
    simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6153 (p : Pattern) (guard : d1095 p = 1) : d536 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6145 p hg
    simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6152 p hg
    simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6154 (p : Pattern) (guard : d1095 p = 1) : d537 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6134 p hg
    simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6153 p hg
    simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6155 (p : Pattern) (guard : d1092 p = 1) : d457 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d1092, d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d1092, d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6156 (p : Pattern) (guard : d1092 p = 1) : d52 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d1092, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6157 (p : Pattern) (guard : d1092 p = 1) : d458 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6155 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6156 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6158 (p : Pattern) (guard : d1092 p = 1) : d460 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d1092, d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d1092, d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6159 (p : Pattern) (guard : d1092 p = 1) : d54 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d1092, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
