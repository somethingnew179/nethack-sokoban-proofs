/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5040 (p : Pattern) (guard : d4203 p = 1) : d265 p ≤ (0 : Int) + d650 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d265, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4979 p hg
    simpa only [d265, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d265, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5039 p hg
    simpa only [d265, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5041 (p : Pattern) (guard : d4203 p = 1) : d266 p ≤ (0 : Int) + d651 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d266, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5018 p hg
    simpa only [d266, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d266, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5040 p hg
    simpa only [d266, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5042 (p : Pattern) (guard : d4203 p = 1) : d267 p ≤ (0 : Int) + d652 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d267, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5002 p hg
    simpa only [d267, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d267, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5041 p hg
    simpa only [d267, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5043 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d324 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5044 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1504 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d16, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d16, d1504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d16, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5043 p hg
    simpa only [d4206, d16, d1504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5045 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d336 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5046 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1505 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d16, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d16, d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d16, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5045 p hg
    simpa only [d4206, d16, d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5047 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1506 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5044 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5046 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5048 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d343 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5049 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d16, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d16, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d16, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5048 p hg
    simpa only [d4206, d16, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5050 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5051 (p : Pattern) (guard : d4206 p = 1) : d20 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4206, d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d4206, d20, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5052 (p : Pattern) (guard : d4206 p = 1) : d21 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d21, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5049 p hg
    simpa only [d21, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d21, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d21, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5053 (p : Pattern) (guard : d4206 p = 1) : d22 p ≤ (0 : Int) + d1509 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d22, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5047 p hg
    simpa only [d22, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d22, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5052 p hg
    simpa only [d22, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5054 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5055 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d4206, d16, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5056 (p : Pattern) (guard : d4206 p = 1) : d21 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d21, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5057 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5058 (p : Pattern) (guard : d4206 p = 1) : d26 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4206, d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d4206, d26, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5059 (p : Pattern) (guard : d4206 p = 1) : d27 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d27, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5060 (p : Pattern) (guard : d4206 p = 1) : d28 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5059 p hg
    simpa only [d28, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5061 (p : Pattern) (guard : d4206 p = 1) : d29 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d29, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5053 p hg
    simpa only [d29, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d29, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d29, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5062 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5063 (p : Pattern) (guard : d4206 p = 1) : d33 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d33, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d33, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d33, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d4206, d33, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5064 (p : Pattern) (guard : d0 p = 1) : d36 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5065 (p : Pattern) (guard : d4206 p = 1) : d37 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d4206, d37, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5066 (p : Pattern) (guard : d4206 p = 1) : d38 p ≤ (0 : Int) + d46 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5065 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5067 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5068 (p : Pattern) (guard : d4206 p = 1) : d42 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d4206, d42, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5069 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (0 : Int) + d43 p := by
  omega
theorem compare5070 (p : Pattern) (guard : d4206 p = 1) : d44 p ≤ (0 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5068 p hg
    simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5071 (p : Pattern) (guard : d4206 p = 1) : d45 p ≤ (0 : Int) + d1511 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d45, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5066 p hg
    simpa only [d45, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d45, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5070 p hg
    simpa only [d45, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5072 (p : Pattern) (guard : d4206 p = 1) : d50 p ≤ (0 : Int) + d50 p := by
  omega
theorem compare5073 (p : Pattern) (guard : d4206 p = 1) : d51 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d51, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5071 p hg
    simpa only [d51, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d51, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5072 p hg
    simpa only [d51, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5074 (p : Pattern) (guard : d4206 p = 1) : d52 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d52, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5061 p hg
    simpa only [d52, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d52, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d52, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5075 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d359 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5076 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1514 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d16, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d16, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d16, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5075 p hg
    simpa only [d4206, d16, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5077 (p : Pattern) (guard : d4206 p = 1) : d53 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4206, d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d4206, d53, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5078 (p : Pattern) (guard : d4206 p = 1) : d54 p ≤ (0 : Int) + d1515 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d54, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5076 p hg
    simpa only [d54, d1515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d54, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d54, d1515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5079 (p : Pattern) (guard : d4206 p = 1) : d55 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d55, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5080 (p : Pattern) (guard : d4206 p = 1) : d56 p ≤ (0 : Int) + d1516 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d56, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5078 p hg
    simpa only [d56, d1516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d56, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d56, d1516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5081 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5082 (p : Pattern) (guard : d4206 p = 1) : d60 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4206, d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d4206, d60, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5083 (p : Pattern) (guard : d4206 p = 1) : d61 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5082 p hg
    simpa only [d61, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5084 (p : Pattern) (guard : d4206 p = 1) : d62 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4206, d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d4206, d62, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5085 (p : Pattern) (guard : d4206 p = 1) : d63 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d63, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5086 (p : Pattern) (guard : d4206 p = 1) : d64 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5083 p hg
    simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d64, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5087 (p : Pattern) (guard : d4206 p = 1) : d65 p ≤ (0 : Int) + d1517 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d65, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5080 p hg
    simpa only [d65, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d65, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5086 p hg
    simpa only [d65, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5088 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare5089 (p : Pattern) (guard : d4206 p = 1) : d67 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d67, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5065 p hg
    simpa only [d67, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d67, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5088 p hg
    simpa only [d67, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5090 (p : Pattern) (guard : d4206 p = 1) : d68 p ≤ (0 : Int) + d68 p := by
  omega
theorem compare5091 (p : Pattern) (guard : d4206 p = 1) : d69 p ≤ (0 : Int) + d1519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d69, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5089 p hg
    simpa only [d69, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d69, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d69, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5092 (p : Pattern) (guard : d4206 p = 1) : d74 p ≤ (0 : Int) + d74 p := by
  omega
theorem compare5093 (p : Pattern) (guard : d4206 p = 1) : d75 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d75, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d75, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d75, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5092 p hg
    simpa only [d75, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5094 (p : Pattern) (guard : d4206 p = 1) : d76 p ≤ (0 : Int) + d1521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d76, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5087 p hg
    simpa only [d76, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d76, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d76, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5095 (p : Pattern) (guard : d4206 p = 1) : d77 p ≤ (0 : Int) + d1522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d77, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5074 p hg
    simpa only [d77, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d77, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5094 p hg
    simpa only [d77, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5096 (p : Pattern) (guard : d4206 p = 1) : d22 p ≤ (0 : Int) + d1511 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d22, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d22, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d22, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d22, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5097 (p : Pattern) (guard : d4206 p = 1) : d29 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d29, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d29, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d29, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d29, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5098 (p : Pattern) (guard : d4206 p = 1) : d78 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d78, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4206, d78, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d78, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d4206, d78, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5099 (p : Pattern) (guard : d4206 p = 1) : d79 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d79, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d79, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d79, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5098 p hg
    simpa only [d79, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5100 (p : Pattern) (guard : d4206 p = 1) : d80 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d80, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5099 p hg
    simpa only [d80, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d80, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d80, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5101 (p : Pattern) (guard : d4206 p = 1) : d81 p ≤ (0 : Int) + d1523 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d81, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5100 p hg
    simpa only [d81, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d81, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d81, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5102 (p : Pattern) (guard : d4206 p = 1) : d82 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d82, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5097 p hg
    simpa only [d82, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d82, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5101 p hg
    simpa only [d82, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5103 (p : Pattern) (guard : d4206 p = 1) : d54 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d54, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d54, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d54, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d54, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5104 (p : Pattern) (guard : d4206 p = 1) : d56 p ≤ (0 : Int) + d1519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d56, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5103 p hg
    simpa only [d56, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d56, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d56, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5105 (p : Pattern) (guard : d4206 p = 1) : d65 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d65, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5104 p hg
    simpa only [d65, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d65, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5086 p hg
    simpa only [d65, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5106 (p : Pattern) (guard : d4206 p = 1) : d83 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d83, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5098 p hg
    simpa only [d83, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d83, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d83, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5107 (p : Pattern) (guard : d4206 p = 1) : d84 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d84, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5106 p hg
    simpa only [d84, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d84, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d84, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5108 (p : Pattern) (guard : d4206 p = 1) : d85 p ≤ (0 : Int) + d1525 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d85, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5107 p hg
    simpa only [d85, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d85, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d85, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5109 (p : Pattern) (guard : d4206 p = 1) : d86 p ≤ (0 : Int) + d1526 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d86, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d86, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d86, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5108 p hg
    simpa only [d86, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5110 (p : Pattern) (guard : d4206 p = 1) : d87 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d87, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5102 p hg
    simpa only [d87, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d87, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5109 p hg
    simpa only [d87, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5111 (p : Pattern) (guard : d4206 p = 1) : d88 p ≤ (0 : Int) + d1528 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d88, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5095 p hg
    simpa only [d88, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d88, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d88, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5112 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5049 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5113 (p : Pattern) (guard : d4206 p = 1) : d22 p ≤ (0 : Int) + d1530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d22, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5112 p hg
    simpa only [d22, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d22, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d22, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5114 (p : Pattern) (guard : d4206 p = 1) : d29 p ≤ (0 : Int) + d1531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d29, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5113 p hg
    simpa only [d29, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d29, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d29, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5115 (p : Pattern) (guard : d4206 p = 1) : d82 p ≤ (0 : Int) + d1532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d82, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d82, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d82, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5101 p hg
    simpa only [d82, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5116 (p : Pattern) (guard : d4206 p = 1) : d87 p ≤ (0 : Int) + d1533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d87, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5115 p hg
    simpa only [d87, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d87, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5109 p hg
    simpa only [d87, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5117 (p : Pattern) (guard : d4206 p = 1) : d89 p ≤ (0 : Int) + d1534 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d89, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d89, d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d89, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d89, d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5118 (p : Pattern) (guard : d4206 p = 1) : d90 p ≤ (0 : Int) + d1535 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d90, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5117 p hg
    simpa only [d90, d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d90, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d90, d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5119 (p : Pattern) (guard : d4206 p = 1) : d91 p ≤ (0 : Int) + d1536 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d91, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d91, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d91, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d91, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5120 (p : Pattern) (guard : d4206 p = 1) : d92 p ≤ (0 : Int) + d1537 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d92, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d92, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d92, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d92, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5121 (p : Pattern) (guard : d4206 p = 1) : d93 p ≤ (0 : Int) + d1538 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d93, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5122 (p : Pattern) (guard : d4206 p = 1) : d94 p ≤ (0 : Int) + d1539 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d94, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5120 p hg
    simpa only [d94, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d94, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5121 p hg
    simpa only [d94, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5123 (p : Pattern) (guard : d4206 p = 1) : d95 p ≤ (0 : Int) + d1540 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5121 p hg
    simpa only [d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5124 (p : Pattern) (guard : d4206 p = 1) : d96 p ≤ (0 : Int) + d1541 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d96, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5122 p hg
    simpa only [d96, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d96, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d96, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5125 (p : Pattern) (guard : d4206 p = 1) : d97 p ≤ (0 : Int) + d1542 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d97, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5116 p hg
    simpa only [d97, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d97, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5124 p hg
    simpa only [d97, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5126 (p : Pattern) (guard : d4206 p = 1) : d98 p ≤ (0 : Int) + d1543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d98, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5111 p hg
    simpa only [d98, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d98, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5125 p hg
    simpa only [d98, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5127 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1544 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5046 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5128 (p : Pattern) (guard : d4206 p = 1) : d22 p ≤ (0 : Int) + d1545 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d22, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5127 p hg
    simpa only [d22, d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d22, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d22, d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5129 (p : Pattern) (guard : d4206 p = 1) : d29 p ≤ (0 : Int) + d1546 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d29, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5128 p hg
    simpa only [d29, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d29, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d29, d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5130 (p : Pattern) (guard : d4206 p = 1) : d52 p ≤ (0 : Int) + d1547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d52, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5129 p hg
    simpa only [d52, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d52, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d52, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5131 (p : Pattern) (guard : d4206 p = 1) : d76 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5132 (p : Pattern) (guard : d4206 p = 1) : d77 p ≤ (0 : Int) + d1548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d77, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5130 p hg
    simpa only [d77, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d77, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5131 p hg
    simpa only [d77, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5133 (p : Pattern) (guard : d4206 p = 1) : d88 p ≤ (0 : Int) + d1549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d88, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5132 p hg
    simpa only [d88, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d88, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d88, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5134 (p : Pattern) (guard : d4206 p = 1) : d99 p ≤ (0 : Int) + d1550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d99, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d99, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d99, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d99, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5135 (p : Pattern) (guard : d4206 p = 1) : d100 p ≤ (0 : Int) + d1551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d100, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5133 p hg
    simpa only [d100, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d100, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5134 p hg
    simpa only [d100, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5136 (p : Pattern) (guard : d4206 p = 1) : d101 p ≤ (0 : Int) + d1552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d101, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d101, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d101, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5135 p hg
    simpa only [d101, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5137 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d353 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5138 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d16, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d16, d1553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d16, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5137 p hg
    simpa only [d4206, d16, d1553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5139 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d1554 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5049 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5140 (p : Pattern) (guard : d4206 p = 1) : d22 p ≤ (0 : Int) + d1555 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d22, d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5139 p hg
    simpa only [d22, d1555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d22, d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d22, d1555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5141 (p : Pattern) (guard : d4206 p = 1) : d29 p ≤ (0 : Int) + d1556 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d29, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d29, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d29, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d29, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5142 (p : Pattern) (guard : d4206 p = 1) : d52 p ≤ (0 : Int) + d1557 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d52, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5141 p hg
    simpa only [d52, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d52, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d52, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5143 (p : Pattern) (guard : d4206 p = 1) : d54 p ≤ (0 : Int) + d1558 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d54, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5046 p hg
    simpa only [d54, d1558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d54, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d54, d1558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5144 (p : Pattern) (guard : d4206 p = 1) : d56 p ≤ (0 : Int) + d1559 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d56, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5143 p hg
    simpa only [d56, d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d56, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d56, d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5145 (p : Pattern) (guard : d4206 p = 1) : d65 p ≤ (0 : Int) + d1560 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d65, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5144 p hg
    simpa only [d65, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d65, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5086 p hg
    simpa only [d65, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5146 (p : Pattern) (guard : d4206 p = 1) : d76 p ≤ (0 : Int) + d1561 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d76, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5145 p hg
    simpa only [d76, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d76, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d76, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5147 (p : Pattern) (guard : d4206 p = 1) : d77 p ≤ (0 : Int) + d1562 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d77, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5142 p hg
    simpa only [d77, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d77, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5146 p hg
    simpa only [d77, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5148 (p : Pattern) (guard : d4206 p = 1) : d88 p ≤ (0 : Int) + d1563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d88, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5147 p hg
    simpa only [d88, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d88, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d88, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5149 (p : Pattern) (guard : d4206 p = 1) : d97 p ≤ (0 : Int) + d1564 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d97, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d97, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d97, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5124 p hg
    simpa only [d97, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5150 (p : Pattern) (guard : d4206 p = 1) : d98 p ≤ (0 : Int) + d1565 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d98, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d98, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d98, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5149 p hg
    simpa only [d98, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5151 (p : Pattern) (guard : d4206 p = 1) : d52 p ≤ (0 : Int) + d1566 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d52, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d52, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d52, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d52, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5152 (p : Pattern) (guard : d4206 p = 1) : d77 p ≤ (0 : Int) + d1567 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d77, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5151 p hg
    simpa only [d77, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d77, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5131 p hg
    simpa only [d77, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5153 (p : Pattern) (guard : d4206 p = 1) : d88 p ≤ (0 : Int) + d1568 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d88, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5152 p hg
    simpa only [d88, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d88, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d88, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5154 (p : Pattern) (guard : d4206 p = 1) : d100 p ≤ (0 : Int) + d1569 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d100, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5153 p hg
    simpa only [d100, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d100, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5134 p hg
    simpa only [d100, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5155 (p : Pattern) (guard : d4206 p = 1) : d101 p ≤ (0 : Int) + d1570 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d101, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5150 p hg
    simpa only [d101, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d101, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5154 p hg
    simpa only [d101, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5156 (p : Pattern) (guard : d4206 p = 1) : d101 p ≤ (0 : Int) + d1571 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5136 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5155 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5157 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d353 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5158 (p : Pattern) (guard : d4206 p = 1) : d105 p ≤ (0 : Int) + d1572 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d105, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d105, d1572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d105, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5157 p hg
    simpa only [d4206, d105, d1572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5159 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d343 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5160 (p : Pattern) (guard : d4206 p = 1) : d105 p ≤ (0 : Int) + d1573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d105, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d105, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d105, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5159 p hg
    simpa only [d4206, d105, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5161 (p : Pattern) (guard : d4206 p = 1) : d105 p ≤ (0 : Int) + d1574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5158 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5160 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5162 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5163 (p : Pattern) (guard : d4206 p = 1) : d105 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d4206, d105, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5164 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5165 (p : Pattern) (guard : d4206 p = 1) : d109 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4206, d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d4206, d109, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5166 (p : Pattern) (guard : d4206 p = 1) : d110 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d110, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5167 (p : Pattern) (guard : d4206 p = 1) : d111 p ≤ (0 : Int) + d1575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d111, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5161 p hg
    simpa only [d111, d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d111, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d111, d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5168 (p : Pattern) (guard : d4206 p = 1) : d112 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5082 p hg
    simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d112, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5169 (p : Pattern) (guard : d4206 p = 1) : d113 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5168 p hg
    simpa only [d113, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5170 (p : Pattern) (guard : d4206 p = 1) : d114 p ≤ (0 : Int) + d1576 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d114, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5167 p hg
    simpa only [d114, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d114, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d114, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5171 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5172 (p : Pattern) (guard : d4206 p = 1) : d118 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d4206, d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5173 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5174 (p : Pattern) (guard : d4206 p = 1) : d122 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d122, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d122, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d122, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d4206, d122, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5175 (p : Pattern) (guard : d4206 p = 1) : d123 p ≤ (0 : Int) + d124 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5172 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5174 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5176 (p : Pattern) (guard : d4206 p = 1) : d126 p ≤ (0 : Int) + d126 p := by
  omega
theorem compare5177 (p : Pattern) (guard : d4206 p = 1) : d127 p ≤ (0 : Int) + d1577 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d127, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5175 p hg
    simpa only [d127, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d127, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5176 p hg
    simpa only [d127, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5178 (p : Pattern) (guard : d4206 p = 1) : d129 p ≤ (0 : Int) + d129 p := by
  omega
theorem compare5179 (p : Pattern) (guard : d4206 p = 1) : d130 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d130, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5177 p hg
    simpa only [d130, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d130, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5178 p hg
    simpa only [d130, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
