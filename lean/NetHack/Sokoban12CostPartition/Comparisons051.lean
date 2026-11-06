/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7140 (p : Pattern) (guard : d1314 p = 1) : d18 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1311 p = 1 := by simpa only [d1314, d18, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7139 p hg
    simpa only [d1314, d18, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1314, d18, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6665 p hg
    simpa only [d1314, d18, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7141 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7142 (p : Pattern) (guard : d1317 p = 1) : d18 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1314 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7140 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7141 p hg
    simpa only [d1317, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7143 (p : Pattern) (guard : d1320 p = 1) : d18 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1317 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7142 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7141 p hg
    simpa only [d1320, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7144 (p : Pattern) (guard : d1321 p = 1) : d22 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6356 p hg
    simpa only [d1321, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7143 p hg
    simpa only [d1321, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7145 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7146 (p : Pattern) (guard : d1323 p = 1) : d377 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d1323, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7145 p hg
    simpa only [d1323, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7147 (p : Pattern) (guard : d1324 p = 1) : d378 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d378, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7144 p hg
    simpa only [d1324, d378, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d378, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7146 p hg
    simpa only [d1324, d378, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7148 (p : Pattern) (guard : d1323 p = 1) : d22 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d1323, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7141 p hg
    simpa only [d1323, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7149 (p : Pattern) (guard : d0 p = 1) : d377 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7150 (p : Pattern) (guard : d1326 p = 1) : d378 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7148 p hg
    simpa only [d1326, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7149 p hg
    simpa only [d1326, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7151 (p : Pattern) (guard : d1327 p = 1) : d378 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7147 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7150 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7152 (p : Pattern) (guard : d0 p = 1) : d378 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7153 (p : Pattern) (guard : d1329 p = 1) : d378 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7150 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7152 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7154 (p : Pattern) (guard : d1330 p = 1) : d378 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7153 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7155 (p : Pattern) (guard : d1331 p = 1) : d379 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7138 p hg
    simpa only [d1331, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7154 p hg
    simpa only [d1331, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7156 (p : Pattern) (guard : d1323 p = 1) : d380 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6398 p hg
    simpa only [d1323, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d1323, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7157 (p : Pattern) (guard : d1324 p = 1) : d381 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d1324, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7156 p hg
    simpa only [d1324, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7158 (p : Pattern) (guard : d0 p = 1) : d380 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7159 (p : Pattern) (guard : d1326 p = 1) : d381 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7134 p hg
    simpa only [d1326, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d1326, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7160 (p : Pattern) (guard : d1327 p = 1) : d381 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7157 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7159 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7161 (p : Pattern) (guard : d0 p = 1) : d383 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7162 (p : Pattern) (guard : d1329 p = 1) : d384 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7159 p hg
    simpa only [d1329, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7161 p hg
    simpa only [d1329, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7163 (p : Pattern) (guard : d1330 p = 1) : d385 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7160 p hg
    simpa only [d1330, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7162 p hg
    simpa only [d1330, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7164 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7165 (p : Pattern) (guard : d1326 p = 1) : d387 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7148 p hg
    simpa only [d1326, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d1326, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7166 (p : Pattern) (guard : d0 p = 1) : d387 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7167 (p : Pattern) (guard : d1329 p = 1) : d387 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7165 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7168 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7169 (p : Pattern) (guard : d1332 p = 1) : d391 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d1332, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d1332, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7170 (p : Pattern) (guard : d1333 p = 1) : d392 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7163 p hg
    simpa only [d1333, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7169 p hg
    simpa only [d1333, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7171 (p : Pattern) (guard : d1334 p = 1) : d393 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d393, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7155 p hg
    simpa only [d1334, d393, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d393, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7170 p hg
    simpa only [d1334, d393, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7172 (p : Pattern) (guard : d1326 p = 1) : d380 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7156 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7173 (p : Pattern) (guard : d1329 p = 1) : d380 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7172 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7174 (p : Pattern) (guard : d1330 p = 1) : d394 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7137 p hg
    simpa only [d1330, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d1330, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7175 (p : Pattern) (guard : d1332 p = 1) : d395 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7153 p hg
    simpa only [d1332, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d1332, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7176 (p : Pattern) (guard : d1333 p = 1) : d396 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7175 p hg
    simpa only [d1333, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7177 (p : Pattern) (guard : d1332 p = 1) : d397 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7162 p hg
    simpa only [d1332, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d1332, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7178 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7179 (p : Pattern) (guard : d1335 p = 1) : d399 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7177 p hg
    simpa only [d1335, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d1335, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7180 (p : Pattern) (guard : d1336 p = 1) : d400 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7176 p hg
    simpa only [d1336, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7179 p hg
    simpa only [d1336, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7181 (p : Pattern) (guard : d1337 p = 1) : d401 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d401, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7171 p hg
    simpa only [d1337, d401, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d401, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7180 p hg
    simpa only [d1337, d401, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7182 (p : Pattern) (guard : d1332 p = 1) : d380 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7183 (p : Pattern) (guard : d1335 p = 1) : d402 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7182 p hg
    simpa only [d1335, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d1335, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7184 (p : Pattern) (guard : d0 p = 1) : d402 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7185 (p : Pattern) (guard : d1338 p = 1) : d402 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7183 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7186 (p : Pattern) (guard : d1339 p = 1) : d403 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7180 p hg
    simpa only [d1339, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7185 p hg
    simpa only [d1339, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7187 (p : Pattern) (guard : d1340 p = 1) : d404 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d404, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7181 p hg
    simpa only [d1340, d404, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d404, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7186 p hg
    simpa only [d1340, d404, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7188 (p : Pattern) (guard : d0 p = 1) : d406 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7189 (p : Pattern) (guard : d1329 p = 1) : d407 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7136 p hg
    simpa only [d1329, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d1329, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7190 (p : Pattern) (guard : d1330 p = 1) : d408 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7137 p hg
    simpa only [d1330, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7189 p hg
    simpa only [d1330, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7191 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7192 (p : Pattern) (guard : d1332 p = 1) : d412 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7153 p hg
    simpa only [d1332, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7191 p hg
    simpa only [d1332, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7193 (p : Pattern) (guard : d1333 p = 1) : d413 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7190 p hg
    simpa only [d1333, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7192 p hg
    simpa only [d1333, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7194 (p : Pattern) (guard : d1336 p = 1) : d414 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7193 p hg
    simpa only [d1336, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7183 p hg
    simpa only [d1336, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7195 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7196 (p : Pattern) (guard : d1326 p = 1) : d415 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7134 p hg
    simpa only [d1326, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7195 p hg
    simpa only [d1326, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7197 (p : Pattern) (guard : d1329 p = 1) : d416 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7196 p hg
    simpa only [d1329, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d1329, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7198 (p : Pattern) (guard : d1332 p = 1) : d417 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7197 p hg
    simpa only [d1332, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d1332, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7199 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7200 (p : Pattern) (guard : d1335 p = 1) : d421 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7198 p hg
    simpa only [d1335, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7199 p hg
    simpa only [d1335, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7201 (p : Pattern) (guard : d1338 p = 1) : d422 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7200 p hg
    simpa only [d1338, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d1338, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7202 (p : Pattern) (guard : d1339 p = 1) : d423 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7194 p hg
    simpa only [d1339, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7201 p hg
    simpa only [d1339, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7203 (p : Pattern) (guard : d1332 p = 1) : d424 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7189 p hg
    simpa only [d1332, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d1332, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7204 (p : Pattern) (guard : d0 p = 1) : d425 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7205 (p : Pattern) (guard : d1335 p = 1) : d426 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7203 p hg
    simpa only [d1335, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7204 p hg
    simpa only [d1335, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7206 (p : Pattern) (guard : d1338 p = 1) : d427 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7205 p hg
    simpa only [d1338, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d1338, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7207 (p : Pattern) (guard : d1341 p = 1) : d428 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7206 p hg
    simpa only [d1341, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d1341, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7208 (p : Pattern) (guard : d1342 p = 1) : d429 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7202 p hg
    simpa only [d1342, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7207 p hg
    simpa only [d1342, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7209 (p : Pattern) (guard : d1343 p = 1) : d430 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d430, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7187 p hg
    simpa only [d1343, d430, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d430, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7208 p hg
    simpa only [d1343, d430, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7210 (p : Pattern) (guard : d1321 p = 1) : d19 p ≤ (0 : Int) + d1346 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1318 p = 1 := by simpa only [d1321, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7122 p hg
    simpa only [d1321, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1320 p = 1 := by simpa only [d1321, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7143 p hg
    simpa only [d1321, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7211 (p : Pattern) (guard : d1323 p = 1) : d266 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d1323, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7145 p hg
    simpa only [d1323, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7212 (p : Pattern) (guard : d1324 p = 1) : d267 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d267, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7210 p hg
    simpa only [d1324, d267, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d267, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7211 p hg
    simpa only [d1324, d267, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7213 (p : Pattern) (guard : d1323 p = 1) : d19 p ≤ (0 : Int) + d5 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1320 p = 1 := by simpa only [d1323, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7128 p hg
    simpa only [d1323, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1323, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7141 p hg
    simpa only [d1323, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7214 (p : Pattern) (guard : d0 p = 1) : d266 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7215 (p : Pattern) (guard : d1326 p = 1) : d267 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7213 p hg
    simpa only [d1326, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7214 p hg
    simpa only [d1326, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7216 (p : Pattern) (guard : d1327 p = 1) : d267 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7212 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7217 (p : Pattern) (guard : d0 p = 1) : d267 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7218 (p : Pattern) (guard : d1329 p = 1) : d267 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7217 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7219 (p : Pattern) (guard : d1330 p = 1) : d267 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7216 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7218 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7220 (p : Pattern) (guard : d1331 p = 1) : d268 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d1331, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7219 p hg
    simpa only [d1331, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7221 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7222 (p : Pattern) (guard : d1326 p = 1) : d270 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1323 p = 1 := by simpa only [d1326, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7213 p hg
    simpa only [d1326, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d1326, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7223 (p : Pattern) (guard : d0 p = 1) : d270 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7224 (p : Pattern) (guard : d1329 p = 1) : d270 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7223 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7225 (p : Pattern) (guard : d0 p = 1) : d277 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7226 (p : Pattern) (guard : d1332 p = 1) : d278 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7224 p hg
    simpa only [d1332, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7225 p hg
    simpa only [d1332, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7227 (p : Pattern) (guard : d1333 p = 1) : d279 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6405 p hg
    simpa only [d1333, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7226 p hg
    simpa only [d1333, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7228 (p : Pattern) (guard : d1334 p = 1) : d280 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d280, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d1334, d280, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d280, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d1334, d280, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7229 (p : Pattern) (guard : d1332 p = 1) : d281 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7218 p hg
    simpa only [d1332, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d1332, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7230 (p : Pattern) (guard : d1333 p = 1) : d282 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d1333, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7229 p hg
    simpa only [d1333, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7231 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7232 (p : Pattern) (guard : d1335 p = 1) : d284 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6419 p hg
    simpa only [d1335, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7231 p hg
    simpa only [d1335, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7233 (p : Pattern) (guard : d1336 p = 1) : d285 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7230 p hg
    simpa only [d1336, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7232 p hg
    simpa only [d1336, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7234 (p : Pattern) (guard : d1337 p = 1) : d286 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d286, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d1337, d286, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d286, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7233 p hg
    simpa only [d1337, d286, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7235 (p : Pattern) (guard : d1335 p = 1) : d287 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d1335, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d1335, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7236 (p : Pattern) (guard : d0 p = 1) : d287 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7237 (p : Pattern) (guard : d1338 p = 1) : d287 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7235 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7238 (p : Pattern) (guard : d1339 p = 1) : d288 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7233 p hg
    simpa only [d1339, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7237 p hg
    simpa only [d1339, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7239 (p : Pattern) (guard : d1340 p = 1) : d289 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d289, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7234 p hg
    simpa only [d1340, d289, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d289, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7238 p hg
    simpa only [d1340, d289, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7240 (p : Pattern) (guard : d0 p = 1) : d294 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7241 (p : Pattern) (guard : d1332 p = 1) : d295 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7218 p hg
    simpa only [d1332, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7240 p hg
    simpa only [d1332, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7242 (p : Pattern) (guard : d1333 p = 1) : d296 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d1333, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d1333, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7243 (p : Pattern) (guard : d1336 p = 1) : d297 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7242 p hg
    simpa only [d1336, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7235 p hg
    simpa only [d1336, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7244 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7245 (p : Pattern) (guard : d1335 p = 1) : d301 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6440 p hg
    simpa only [d1335, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7244 p hg
    simpa only [d1335, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7246 (p : Pattern) (guard : d1338 p = 1) : d302 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7245 p hg
    simpa only [d1338, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d1338, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7247 (p : Pattern) (guard : d1339 p = 1) : d303 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7243 p hg
    simpa only [d1339, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7246 p hg
    simpa only [d1339, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7248 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7249 (p : Pattern) (guard : d1335 p = 1) : d305 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1335, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d1335, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1335, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7248 p hg
    simpa only [d1335, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7250 (p : Pattern) (guard : d1338 p = 1) : d306 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7249 p hg
    simpa only [d1338, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d1338, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7251 (p : Pattern) (guard : d1341 p = 1) : d307 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7250 p hg
    simpa only [d1341, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d1341, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7252 (p : Pattern) (guard : d1342 p = 1) : d308 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7247 p hg
    simpa only [d1342, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7251 p hg
    simpa only [d1342, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7253 (p : Pattern) (guard : d1343 p = 1) : d309 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d309, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7239 p hg
    simpa only [d1343, d309, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d309, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7252 p hg
    simpa only [d1343, d309, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7254 (p : Pattern) (guard : d1322 p = 1) : d106 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1319 p = 1 := by simpa only [d1322, d106, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6357 p hg
    simpa only [d1322, d106, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1321 p = 1 := by simpa only [d1322, d106, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d1322, d106, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7255 (p : Pattern) (guard : d1325 p = 1) : d106 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1322 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7254 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1324 p = 1 := by simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d1325, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7256 (p : Pattern) (guard : d1328 p = 1) : d106 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7255 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d1328, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7257 (p : Pattern) (guard : d1324 p = 1) : d109 p ≤ (0 : Int) + d1347 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1321 p = 1 := by simpa only [d1324, d109, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d1324, d109, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1323 p = 1 := by simpa only [d1324, d109, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6520 p hg
    simpa only [d1324, d109, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7258 (p : Pattern) (guard : d1327 p = 1) : d109 p ≤ (0 : Int) + d1348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1324 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7257 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1326 p = 1 := by simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d1327, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7259 (p : Pattern) (guard : d1330 p = 1) : d109 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7258 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d1330, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7260 (p : Pattern) (guard : d1331 p = 1) : d227 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7256 p hg
    simpa only [d1331, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7259 p hg
    simpa only [d1331, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7261 (p : Pattern) (guard : d1334 p = 1) : d227 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7260 p hg
    simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d1334, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7262 (p : Pattern) (guard : d1330 p = 1) : d229 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d1330, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1330, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7263 (p : Pattern) (guard : d1332 p = 1) : d230 p ≤ (0 : Int) + d5 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1332, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d1332, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d1332, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7264 (p : Pattern) (guard : d1333 p = 1) : d231 p ≤ (0 : Int) + d5 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1330 p = 1 := by simpa only [d1333, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7262 p hg
    simpa only [d1333, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1332 p = 1 := by simpa only [d1333, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7263 p hg
    simpa only [d1333, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7265 (p : Pattern) (guard : d1336 p = 1) : d231 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7264 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7111 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7266 (p : Pattern) (guard : d1337 p = 1) : d366 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d366, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7261 p hg
    simpa only [d1337, d366, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d366, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7265 p hg
    simpa only [d1337, d366, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7267 (p : Pattern) (guard : d1339 p = 1) : d367 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7265 p hg
    simpa only [d1339, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1339, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7268 (p : Pattern) (guard : d1340 p = 1) : d368 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1337 p = 1 := by simpa only [d1340, d368, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d1340, d368, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1339 p = 1 := by simpa only [d1340, d368, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7267 p hg
    simpa only [d1340, d368, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7269 (p : Pattern) (guard : d1336 p = 1) : d369 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1333 p = 1 := by simpa only [d1336, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d1336, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1335 p = 1 := by simpa only [d1336, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d1336, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7270 (p : Pattern) (guard : d1338 p = 1) : d370 p ≤ (0 : Int) + d5 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1338, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7111 p hg
    simpa only [d1338, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1338, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1338, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7271 (p : Pattern) (guard : d1339 p = 1) : d371 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1336 p = 1 := by simpa only [d1339, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7269 p hg
    simpa only [d1339, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1338 p = 1 := by simpa only [d1339, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d1339, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7272 (p : Pattern) (guard : d1341 p = 1) : d372 p ≤ (0 : Int) + d5 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1338 p = 1 := by simpa only [d1341, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d1341, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1341, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1341, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7273 (p : Pattern) (guard : d1342 p = 1) : d373 p ≤ (0 : Int) + d5 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1339 p = 1 := by simpa only [d1342, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7271 p hg
    simpa only [d1342, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1341 p = 1 := by simpa only [d1342, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7272 p hg
    simpa only [d1342, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7274 (p : Pattern) (guard : d1343 p = 1) : d374 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1340 p = 1 := by simpa only [d1343, d374, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d1343, d374, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1342 p = 1 := by simpa only [d1343, d374, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d1343, d374, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7275 (p : Pattern) (guard : d1328 p = 1) : d68 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1325 p = 1 := by simpa only [d1328, d68, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6372 p hg
    simpa only [d1328, d68, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, d68, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6517 p hg
    simpa only [d1328, d68, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7276 (p : Pattern) (guard : d1330 p = 1) : d69 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1327 p = 1 := by simpa only [d1330, d69, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6393 p hg
    simpa only [d1330, d69, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1329 p = 1 := by simpa only [d1330, d69, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6522 p hg
    simpa only [d1330, d69, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7277 (p : Pattern) (guard : d1331 p = 1) : d70 p ≤ (0 : Int) + d1349 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1328 p = 1 := by simpa only [d1331, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d1331, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7276 p hg
    simpa only [d1331, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7278 (p : Pattern) (guard : d1334 p = 1) : d232 p ≤ (0 : Int) + d1350 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1331 p = 1 := by simpa only [d1334, d232, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7277 p hg
    simpa only [d1334, d232, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, d232, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7264 p hg
    simpa only [d1334, d232, d1350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7279 (p : Pattern) (guard : d1337 p = 1) : d315 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1334 p = 1 := by simpa only [d1337, d315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d1337, d315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1336 p = 1 := by simpa only [d1337, d315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d1337, d315, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
