/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11060 (p : Pattern) (guard : d0 p = 1) : d293 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11061 (p : Pattern) (guard : d4765 p = 1) : d1489 p ≤ (0 : Int) + d269 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11059 p hg
    simpa only [d4765, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11060 p hg
    simpa only [d4765, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11062 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d277 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11063 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10940 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11064 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11063 p hg
    simpa only [d132, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d132, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11065 (p : Pattern) (guard : d4147 p = 1) : d1133 p ≤ (0 : Int) + d277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11062 p hg
    simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11064 p hg
    simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11066 (p : Pattern) (guard : d4765 p = 1) : d1490 p ≤ (0 : Int) + d277 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11065 p hg
    simpa only [d4765, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11038 p hg
    simpa only [d4765, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11067 (p : Pattern) (guard : d4765 p = 1) : d1491 p ≤ (0 : Int) + d4889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1491, d4889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11061 p hg
    simpa only [d1491, d4889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1491, d4889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11066 p hg
    simpa only [d1491, d4889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11068 (p : Pattern) (guard : d4765 p = 1) : d1492 p ≤ (0 : Int) + d4890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1492, d4890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11067 p hg
    simpa only [d1492, d4890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1492, d4890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10983 p hg
    simpa only [d1492, d4890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11069 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11070 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11071 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d298 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11072 (p : Pattern) (guard : d4147 p = 1) : d132 p ≤ (0 : Int) + d298 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11073 (p : Pattern) (guard : d0 p = 1) : d1385 p ≤ (0 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11074 (p : Pattern) (guard : d4765 p = 1) : d1493 p ≤ (0 : Int) + d298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d4765, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d4765, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11075 (p : Pattern) (guard : d4147 p = 1) : d1137 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8329 p hg
    simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d4147, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11076 (p : Pattern) (guard : d4765 p = 1) : d1138 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11075 p hg
    simpa only [d4765, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11077 (p : Pattern) (guard : d4765 p = 1) : d1494 p ≤ (0 : Int) + d4891 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1494, d4891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11074 p hg
    simpa only [d1494, d4891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1494, d4891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11076 p hg
    simpa only [d1494, d4891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11078 (p : Pattern) (guard : d4147 p = 1) : d109 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11079 (p : Pattern) (guard : d4765 p = 1) : d1140 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11078 p hg
    simpa only [d4765, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11080 (p : Pattern) (guard : d4765 p = 1) : d1141 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11079 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11081 (p : Pattern) (guard : d4765 p = 1) : d1495 p ≤ (0 : Int) + d4892 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1495, d4892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1495, d4892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1495, d4892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11080 p hg
    simpa only [d1495, d4892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11082 (p : Pattern) (guard : d4765 p = 1) : d1496 p ≤ (0 : Int) + d4893 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1496, d4893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d1496, d4893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1496, d4893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11081 p hg
    simpa only [d1496, d4893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11083 (p : Pattern) (guard : d4765 p = 1) : d1497 p ≤ (0 : Int) + d4894 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1497, d4894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11058 p hg
    simpa only [d1497, d4894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1497, d4894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11082 p hg
    simpa only [d1497, d4894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11084 (p : Pattern) (guard : d4765 p = 1) : d1498 p ≤ (0 : Int) + d4895 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1498, d4895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11082 p hg
    simpa only [d1498, d4895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1498, d4895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1498, d4895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11085 (p : Pattern) (guard : d4765 p = 1) : d1499 p ≤ (0 : Int) + d4896 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1499, d4896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11083 p hg
    simpa only [d1499, d4896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1499, d4896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d1499, d4896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11086 (p : Pattern) (guard : d4765 p = 1) : d1500 p ≤ (0 : Int) + d4897 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1500, d4897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11024 p hg
    simpa only [d1500, d4897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1500, d4897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11085 p hg
    simpa only [d1500, d4897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11087 (p : Pattern) (guard : d4765 p = 1) : d1501 p ≤ (0 : Int) + d4898 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1501, d4898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10924 p hg
    simpa only [d1501, d4898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1501, d4898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11086 p hg
    simpa only [d1501, d4898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11088 (p : Pattern) (guard : d4765 p = 1) : d1502 p ≤ (0 : Int) + d4899 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1502, d4899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11023 p hg
    simpa only [d1502, d4899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1502, d4899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11087 p hg
    simpa only [d1502, d4899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11089 (p : Pattern) (guard : d4765 p = 1) : d1503 p ≤ (0 : Int) + d4900 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1503, d4900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11010 p hg
    simpa only [d1503, d4900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1503, d4900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d1503, d4900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11090 (p : Pattern) (guard : d4148 p = 1) : d1399 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1399, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9131 p hg
    simpa only [d1399, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1399, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1399, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11091 (p : Pattern) (guard : d4148 p = 1) : d1400 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1400, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d1400, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1400, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11090 p hg
    simpa only [d1400, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11092 (p : Pattern) (guard : d4148 p = 1) : d1401 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1401, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9135 p hg
    simpa only [d1401, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1401, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4069 p hg
    simpa only [d1401, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11093 (p : Pattern) (guard : d4148 p = 1) : d1402 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1402, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11092 p hg
    simpa only [d1402, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1402, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4071 p hg
    simpa only [d1402, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11094 (p : Pattern) (guard : d4148 p = 1) : d1403 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1403, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11091 p hg
    simpa only [d1403, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1403, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11093 p hg
    simpa only [d1403, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11095 (p : Pattern) (guard : d0 p = 1) : d1409 p ≤ (0 : Int) + d392 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11096 (p : Pattern) (guard : d4303 p = 1) : d1410 p ≤ (0 : Int) + d653 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1410, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11094 p hg
    simpa only [d4303, d1410, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1410, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11095 p hg
    simpa only [d4303, d1410, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11097 (p : Pattern) (guard : d4148 p = 1) : d1411 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1411, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9144 p hg
    simpa only [d1411, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1411, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1411, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11098 (p : Pattern) (guard : d4148 p = 1) : d1412 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1412, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d1412, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1412, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11097 p hg
    simpa only [d1412, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11099 (p : Pattern) (guard : d4148 p = 1) : d1413 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1413, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9148 p hg
    simpa only [d1413, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1413, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1413, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11100 (p : Pattern) (guard : d4148 p = 1) : d1414 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1414, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11099 p hg
    simpa only [d1414, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1414, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1414, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11101 (p : Pattern) (guard : d4148 p = 1) : d1415 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1415, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11098 p hg
    simpa only [d1415, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1415, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11100 p hg
    simpa only [d1415, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11102 (p : Pattern) (guard : d0 p = 1) : d1419 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11103 (p : Pattern) (guard : d4303 p = 1) : d1420 p ≤ (0 : Int) + d654 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1420, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1420, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1420, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11102 p hg
    simpa only [d4303, d1420, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11104 (p : Pattern) (guard : d4303 p = 1) : d1421 p ≤ (0 : Int) + d655 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1421, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11096 p hg
    simpa only [d1421, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1421, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11103 p hg
    simpa only [d1421, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11105 (p : Pattern) (guard : d0 p = 1) : d1419 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11106 (p : Pattern) (guard : d4303 p = 1) : d1420 p ≤ (0 : Int) + d656 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1420, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1420, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1420, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d4303, d1420, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11107 (p : Pattern) (guard : d4303 p = 1) : d96 p ≤ (0 : Int) + d657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4090 p hg
    simpa only [d4303, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2241 p hg
    simpa only [d4303, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11108 (p : Pattern) (guard : d4303 p = 1) : d1422 p ≤ (0 : Int) + d658 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1422, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11106 p hg
    simpa only [d1422, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1422, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11107 p hg
    simpa only [d1422, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11109 (p : Pattern) (guard : d4303 p = 1) : d1423 p ≤ (0 : Int) + d659 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1423, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11104 p hg
    simpa only [d1423, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1423, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11108 p hg
    simpa only [d1423, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11110 (p : Pattern) (guard : d0 p = 1) : d1425 p ≤ (0 : Int) + d397 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11111 (p : Pattern) (guard : d4303 p = 1) : d1426 p ≤ (0 : Int) + d660 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1426, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11094 p hg
    simpa only [d4303, d1426, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1426, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11110 p hg
    simpa only [d4303, d1426, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11112 (p : Pattern) (guard : d0 p = 1) : d1419 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11113 (p : Pattern) (guard : d4303 p = 1) : d1420 p ≤ (0 : Int) + d661 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1420, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1420, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1420, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11112 p hg
    simpa only [d4303, d1420, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11114 (p : Pattern) (guard : d4303 p = 1) : d1427 p ≤ (0 : Int) + d662 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1427, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11111 p hg
    simpa only [d1427, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1427, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11113 p hg
    simpa only [d1427, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11115 (p : Pattern) (guard : d0 p = 1) : d1419 p ≤ (0 : Int) + d410 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11116 (p : Pattern) (guard : d4303 p = 1) : d1420 p ≤ (0 : Int) + d663 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1420, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1420, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1420, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11115 p hg
    simpa only [d4303, d1420, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11117 (p : Pattern) (guard : d4303 p = 1) : d1428 p ≤ (0 : Int) + d664 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1428, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11116 p hg
    simpa only [d1428, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1428, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1428, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11118 (p : Pattern) (guard : d4303 p = 1) : d1429 p ≤ (0 : Int) + d665 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1429, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11114 p hg
    simpa only [d1429, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1429, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11117 p hg
    simpa only [d1429, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11119 (p : Pattern) (guard : d4303 p = 1) : d1430 p ≤ (0 : Int) + d666 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1430, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11109 p hg
    simpa only [d1430, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1430, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11118 p hg
    simpa only [d1430, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11120 (p : Pattern) (guard : d0 p = 1) : d1433 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11121 (p : Pattern) (guard : d4303 p = 1) : d1434 p ≤ (0 : Int) + d667 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1434, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11094 p hg
    simpa only [d4303, d1434, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1434, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11120 p hg
    simpa only [d4303, d1434, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11122 (p : Pattern) (guard : d0 p = 1) : d1419 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11123 (p : Pattern) (guard : d4303 p = 1) : d1420 p ≤ (0 : Int) + d668 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1420, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1420, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1420, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11122 p hg
    simpa only [d4303, d1420, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11124 (p : Pattern) (guard : d4303 p = 1) : d1435 p ≤ (0 : Int) + d669 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1435, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11121 p hg
    simpa only [d1435, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1435, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11123 p hg
    simpa only [d1435, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11125 (p : Pattern) (guard : d4303 p = 1) : d96 p ≤ (0 : Int) + d670 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4090 p hg
    simpa only [d4303, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2260 p hg
    simpa only [d4303, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11126 (p : Pattern) (guard : d4303 p = 1) : d1422 p ≤ (0 : Int) + d671 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1422, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11103 p hg
    simpa only [d1422, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1422, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11125 p hg
    simpa only [d1422, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11127 (p : Pattern) (guard : d4303 p = 1) : d1436 p ≤ (0 : Int) + d672 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1436, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11124 p hg
    simpa only [d1436, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1436, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11126 p hg
    simpa only [d1436, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11128 (p : Pattern) (guard : d0 p = 1) : d1425 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11129 (p : Pattern) (guard : d4303 p = 1) : d1426 p ≤ (0 : Int) + d673 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1426, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11094 p hg
    simpa only [d4303, d1426, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1426, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11128 p hg
    simpa only [d4303, d1426, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11130 (p : Pattern) (guard : d0 p = 1) : d1419 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11131 (p : Pattern) (guard : d4303 p = 1) : d1420 p ≤ (0 : Int) + d674 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1420, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1420, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1420, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11130 p hg
    simpa only [d4303, d1420, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11132 (p : Pattern) (guard : d4303 p = 1) : d1427 p ≤ (0 : Int) + d675 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1427, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11129 p hg
    simpa only [d1427, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1427, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11131 p hg
    simpa only [d1427, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11133 (p : Pattern) (guard : d4303 p = 1) : d1428 p ≤ (0 : Int) + d676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1428, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11113 p hg
    simpa only [d1428, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1428, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1428, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11134 (p : Pattern) (guard : d4303 p = 1) : d1429 p ≤ (0 : Int) + d677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1429, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11132 p hg
    simpa only [d1429, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1429, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11133 p hg
    simpa only [d1429, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11135 (p : Pattern) (guard : d4303 p = 1) : d1437 p ≤ (0 : Int) + d678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1437, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11127 p hg
    simpa only [d1437, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1437, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11134 p hg
    simpa only [d1437, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11136 (p : Pattern) (guard : d4303 p = 1) : d1438 p ≤ (0 : Int) + d679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1438, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1438, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1438, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11135 p hg
    simpa only [d1438, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11137 (p : Pattern) (guard : d4148 p = 1) : d1439 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1439, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9218 p hg
    simpa only [d1439, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1439, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1439, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11138 (p : Pattern) (guard : d4148 p = 1) : d1440 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1440, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d1440, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1440, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11137 p hg
    simpa only [d1440, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11139 (p : Pattern) (guard : d4148 p = 1) : d1441 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1441, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9222 p hg
    simpa only [d1441, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1441, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d1441, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11140 (p : Pattern) (guard : d4148 p = 1) : d1442 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1442, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11139 p hg
    simpa only [d1442, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1442, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4130 p hg
    simpa only [d1442, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11141 (p : Pattern) (guard : d4148 p = 1) : d1443 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1443, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11138 p hg
    simpa only [d1443, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1443, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11140 p hg
    simpa only [d1443, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11142 (p : Pattern) (guard : d0 p = 1) : d1448 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11143 (p : Pattern) (guard : d4303 p = 1) : d1449 p ≤ (0 : Int) + d680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1449, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11141 p hg
    simpa only [d4303, d1449, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1449, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11142 p hg
    simpa only [d4303, d1449, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11144 (p : Pattern) (guard : d4148 p = 1) : d1450 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1450, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9231 p hg
    simpa only [d1450, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1450, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1450, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11145 (p : Pattern) (guard : d4148 p = 1) : d1451 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1451, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d1451, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1451, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11144 p hg
    simpa only [d1451, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11146 (p : Pattern) (guard : d4148 p = 1) : d1061 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9235 p hg
    simpa only [d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11147 (p : Pattern) (guard : d4148 p = 1) : d1062 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11146 p hg
    simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11148 (p : Pattern) (guard : d4148 p = 1) : d1452 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1452, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11145 p hg
    simpa only [d1452, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1452, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11147 p hg
    simpa only [d1452, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11149 (p : Pattern) (guard : d0 p = 1) : d1455 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11150 (p : Pattern) (guard : d4303 p = 1) : d1456 p ≤ (0 : Int) + d681 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1456, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d4303, d1456, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1456, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11149 p hg
    simpa only [d4303, d1456, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11151 (p : Pattern) (guard : d4303 p = 1) : d1457 p ≤ (0 : Int) + d682 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1457, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11143 p hg
    simpa only [d1457, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1457, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11150 p hg
    simpa only [d1457, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11152 (p : Pattern) (guard : d0 p = 1) : d1455 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11153 (p : Pattern) (guard : d4303 p = 1) : d1456 p ≤ (0 : Int) + d683 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1456, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d4303, d1456, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1456, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11152 p hg
    simpa only [d4303, d1456, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11154 (p : Pattern) (guard : d4303 p = 1) : d1458 p ≤ (0 : Int) + d684 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1458, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11153 p hg
    simpa only [d1458, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1458, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d1458, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11155 (p : Pattern) (guard : d4303 p = 1) : d1459 p ≤ (0 : Int) + d685 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1459, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11151 p hg
    simpa only [d1459, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1459, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11154 p hg
    simpa only [d1459, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11156 (p : Pattern) (guard : d0 p = 1) : d1461 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11157 (p : Pattern) (guard : d4303 p = 1) : d1462 p ≤ (0 : Int) + d686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1462, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11141 p hg
    simpa only [d4303, d1462, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1462, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11156 p hg
    simpa only [d4303, d1462, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11158 (p : Pattern) (guard : d0 p = 1) : d1455 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11159 (p : Pattern) (guard : d4303 p = 1) : d1456 p ≤ (0 : Int) + d687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1456, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d4303, d1456, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1456, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11158 p hg
    simpa only [d4303, d1456, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11160 (p : Pattern) (guard : d4303 p = 1) : d1463 p ≤ (0 : Int) + d688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1463, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11157 p hg
    simpa only [d1463, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1463, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11159 p hg
    simpa only [d1463, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11161 (p : Pattern) (guard : d0 p = 1) : d1455 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11162 (p : Pattern) (guard : d4303 p = 1) : d1456 p ≤ (0 : Int) + d689 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1456, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d4303, d1456, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1456, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11161 p hg
    simpa only [d4303, d1456, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11163 (p : Pattern) (guard : d4303 p = 1) : d1464 p ≤ (0 : Int) + d690 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1464, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11162 p hg
    simpa only [d1464, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1464, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1464, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11164 (p : Pattern) (guard : d4303 p = 1) : d1465 p ≤ (0 : Int) + d691 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1465, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11160 p hg
    simpa only [d1465, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1465, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11163 p hg
    simpa only [d1465, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11165 (p : Pattern) (guard : d4303 p = 1) : d1466 p ≤ (0 : Int) + d692 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1466, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11155 p hg
    simpa only [d1466, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1466, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11164 p hg
    simpa only [d1466, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11166 (p : Pattern) (guard : d4303 p = 1) : d1467 p ≤ (0 : Int) + d693 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1467, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1467, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1467, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11165 p hg
    simpa only [d1467, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11167 (p : Pattern) (guard : d4303 p = 1) : d1468 p ≤ (0 : Int) + d694 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1468, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11136 p hg
    simpa only [d1468, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1468, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11166 p hg
    simpa only [d1468, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11168 (p : Pattern) (guard : d0 p = 1) : d1471 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11169 (p : Pattern) (guard : d4303 p = 1) : d1472 p ≤ (0 : Int) + d674 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1472, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1472, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1472, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11168 p hg
    simpa only [d4303, d1472, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11170 (p : Pattern) (guard : d4303 p = 1) : d1473 p ≤ (0 : Int) + d675 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1473, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11129 p hg
    simpa only [d1473, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1473, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11169 p hg
    simpa only [d1473, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11171 (p : Pattern) (guard : d0 p = 1) : d1471 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11172 (p : Pattern) (guard : d4303 p = 1) : d1472 p ≤ (0 : Int) + d661 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1472, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11101 p hg
    simpa only [d4303, d1472, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1472, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11171 p hg
    simpa only [d4303, d1472, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11173 (p : Pattern) (guard : d4303 p = 1) : d1474 p ≤ (0 : Int) + d676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1474, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11172 p hg
    simpa only [d1474, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1474, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1474, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11174 (p : Pattern) (guard : d4303 p = 1) : d1475 p ≤ (0 : Int) + d677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1475, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11170 p hg
    simpa only [d1475, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1475, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11173 p hg
    simpa only [d1475, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11175 (p : Pattern) (guard : d4303 p = 1) : d1476 p ≤ (0 : Int) + d678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1476, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11127 p hg
    simpa only [d1476, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1476, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11174 p hg
    simpa only [d1476, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11176 (p : Pattern) (guard : d4303 p = 1) : d1477 p ≤ (0 : Int) + d679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1477, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1477, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1477, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11175 p hg
    simpa only [d1477, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11177 (p : Pattern) (guard : d0 p = 1) : d1461 p ≤ (0 : Int) + d453 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11178 (p : Pattern) (guard : d4303 p = 1) : d1462 p ≤ (0 : Int) + d695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1462, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11141 p hg
    simpa only [d4303, d1462, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1462, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11177 p hg
    simpa only [d4303, d1462, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11179 (p : Pattern) (guard : d0 p = 1) : d1455 p ≤ (0 : Int) + d456 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11180 (p : Pattern) (guard : d4303 p = 1) : d1456 p ≤ (0 : Int) + d696 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1456, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d4303, d1456, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1456, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11179 p hg
    simpa only [d4303, d1456, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11181 (p : Pattern) (guard : d4303 p = 1) : d1463 p ≤ (0 : Int) + d697 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1463, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11178 p hg
    simpa only [d1463, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1463, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11180 p hg
    simpa only [d1463, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11182 (p : Pattern) (guard : d0 p = 1) : d1455 p ≤ (0 : Int) + d461 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11183 (p : Pattern) (guard : d4303 p = 1) : d1456 p ≤ (0 : Int) + d698 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1456, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11148 p hg
    simpa only [d4303, d1456, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1456, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11182 p hg
    simpa only [d4303, d1456, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11184 (p : Pattern) (guard : d4303 p = 1) : d1458 p ≤ (0 : Int) + d699 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1458, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11183 p hg
    simpa only [d1458, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1458, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d1458, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11185 (p : Pattern) (guard : d4303 p = 1) : d1478 p ≤ (0 : Int) + d700 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1478, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11181 p hg
    simpa only [d1478, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1478, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11184 p hg
    simpa only [d1478, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11186 (p : Pattern) (guard : d4148 p = 1) : d1479 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1479, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9290 p hg
    simpa only [d1479, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1479, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1479, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11187 (p : Pattern) (guard : d4148 p = 1) : d1480 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1480, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d1480, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1480, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11186 p hg
    simpa only [d1480, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11188 (p : Pattern) (guard : d4148 p = 1) : d1481 p ≤ (0 : Int) + d276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1481, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9294 p hg
    simpa only [d1481, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1481, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d1481, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11189 (p : Pattern) (guard : d4148 p = 1) : d1482 p ≤ (0 : Int) + d280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1482, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11188 p hg
    simpa only [d1482, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1482, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4189 p hg
    simpa only [d1482, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11190 (p : Pattern) (guard : d4148 p = 1) : d1483 p ≤ (0 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1483, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11187 p hg
    simpa only [d1483, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1483, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11189 p hg
    simpa only [d1483, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11191 (p : Pattern) (guard : d0 p = 1) : d1487 p ≤ (0 : Int) + d471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11192 (p : Pattern) (guard : d4303 p = 1) : d1488 p ≤ (0 : Int) + d701 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1488, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11190 p hg
    simpa only [d4303, d1488, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1488, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11191 p hg
    simpa only [d4303, d1488, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11193 (p : Pattern) (guard : d4148 p = 1) : d1489 p ≤ (0 : Int) + d294 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1489, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9302 p hg
    simpa only [d1489, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1489, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4196 p hg
    simpa only [d1489, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11194 (p : Pattern) (guard : d4148 p = 1) : d1490 p ≤ (0 : Int) + d295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1490, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9305 p hg
    simpa only [d1490, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1490, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d1490, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11195 (p : Pattern) (guard : d4148 p = 1) : d1491 p ≤ (0 : Int) + d296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1491, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11193 p hg
    simpa only [d1491, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1491, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11194 p hg
    simpa only [d1491, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11196 (p : Pattern) (guard : d4148 p = 1) : d1492 p ≤ (0 : Int) + d297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1492, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11195 p hg
    simpa only [d1492, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1492, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11147 p hg
    simpa only [d1492, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11197 (p : Pattern) (guard : d0 p = 1) : d1495 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11198 (p : Pattern) (guard : d4303 p = 1) : d1496 p ≤ (0 : Int) + d702 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1496, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11196 p hg
    simpa only [d4303, d1496, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1496, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11197 p hg
    simpa only [d4303, d1496, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11199 (p : Pattern) (guard : d4303 p = 1) : d1497 p ≤ (0 : Int) + d703 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1497, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11192 p hg
    simpa only [d1497, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1497, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11198 p hg
    simpa only [d1497, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
