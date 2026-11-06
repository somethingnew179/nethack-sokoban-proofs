/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14140 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (2 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14141 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14140 p hg
    simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14142 (p : Pattern) (guard : d4147 p = 1) : d53 p ≤ (2 : Int) + d20 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14139 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14141 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14143 (p : Pattern) (guard : d4147 p = 1) : d1413 p ≤ (2 : Int) + d1100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1413, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14142 p hg
    simpa only [d1413, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1413, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14055 p hg
    simpa only [d1413, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14144 (p : Pattern) (guard : d4147 p = 1) : d1414 p ≤ (2 : Int) + d1101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1414, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14143 p hg
    simpa only [d1414, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1414, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d1414, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14145 (p : Pattern) (guard : d4147 p = 1) : d1415 p ≤ (2 : Int) + d4362 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1415, d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14138 p hg
    simpa only [d1415, d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1415, d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14144 p hg
    simpa only [d1415, d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14146 (p : Pattern) (guard : d0 p = 1) : d1471 p ≤ (2 : Int) + d4362 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14147 (p : Pattern) (guard : d4304 p = 1) : d1472 p ≤ (2 : Int) + d4362 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14145 p hg
    simpa only [d4304, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14146 p hg
    simpa only [d4304, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14148 (p : Pattern) (guard : d4304 p = 1) : d1473 p ≤ (2 : Int) + d5255 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1473, d5255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14074 p hg
    simpa only [d1473, d5255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1473, d5255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14147 p hg
    simpa only [d1473, d5255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14149 (p : Pattern) (guard : d4304 p = 1) : d1474 p ≤ (2 : Int) + d5256 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1474, d5256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14147 p hg
    simpa only [d1474, d5256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1474, d5256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14076 p hg
    simpa only [d1474, d5256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14150 (p : Pattern) (guard : d4304 p = 1) : d1475 p ≤ (2 : Int) + d5257 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1475, d5257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14148 p hg
    simpa only [d1475, d5257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1475, d5257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14149 p hg
    simpa only [d1475, d5257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14151 (p : Pattern) (guard : d4304 p = 1) : d1476 p ≤ (2 : Int) + d5258 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1476, d5258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14083 p hg
    simpa only [d1476, d5258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1476, d5258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14150 p hg
    simpa only [d1476, d5258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14152 (p : Pattern) (guard : d4304 p = 1) : d1477 p ≤ (2 : Int) + d5259 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1477, d5259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14079 p hg
    simpa only [d1477, d5259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1477, d5259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14151 p hg
    simpa only [d1477, d5259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14153 (p : Pattern) (guard : d4304 p = 1) : d1478 p ≤ (2 : Int) + d5252 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1478, d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14128 p hg
    simpa only [d1478, d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1478, d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14124 p hg
    simpa only [d1478, d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14154 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (2 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14092 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14155 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14154 p hg
    simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14156 (p : Pattern) (guard : d4147 p = 1) : d291 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14087 p hg
    simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14155 p hg
    simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14157 (p : Pattern) (guard : d4147 p = 1) : d1479 p ≤ (2 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1479, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14156 p hg
    simpa only [d1479, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1479, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14096 p hg
    simpa only [d1479, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14158 (p : Pattern) (guard : d4147 p = 1) : d1480 p ≤ (2 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1480, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14089 p hg
    simpa only [d1480, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1480, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14157 p hg
    simpa only [d1480, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14159 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14160 (p : Pattern) (guard : d4147 p = 1) : d269 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14159 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14155 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14161 (p : Pattern) (guard : d0 p = 1) : d272 p ≤ (2 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14162 (p : Pattern) (guard : d1 p = 1) : d274 p ≤ (2 : Int) + d283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6911 p hg
    simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d274, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14163 (p : Pattern) (guard : d4147 p = 1) : d275 p ≤ (2 : Int) + d283 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14161 p hg
    simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14162 p hg
    simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14164 (p : Pattern) (guard : d4147 p = 1) : d1481 p ≤ (2 : Int) + d4373 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1481, d4373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14160 p hg
    simpa only [d1481, d4373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1481, d4373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14163 p hg
    simpa only [d1481, d4373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14165 (p : Pattern) (guard : d0 p = 1) : d277 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14166 (p : Pattern) (guard : d4147 p = 1) : d278 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14165 p hg
    simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14167 (p : Pattern) (guard : d4147 p = 1) : d279 p ≤ (2 : Int) + d4374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d279, d4374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14163 p hg
    simpa only [d279, d4374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d279, d4374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14166 p hg
    simpa only [d279, d4374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14168 (p : Pattern) (guard : d4147 p = 1) : d1482 p ≤ (2 : Int) + d4375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1482, d4375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14164 p hg
    simpa only [d1482, d4375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1482, d4375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14167 p hg
    simpa only [d1482, d4375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14169 (p : Pattern) (guard : d4147 p = 1) : d1483 p ≤ (2 : Int) + d4376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1483, d4376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14158 p hg
    simpa only [d1483, d4376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1483, d4376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14168 p hg
    simpa only [d1483, d4376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14170 (p : Pattern) (guard : d0 p = 1) : d1487 p ≤ (2 : Int) + d4376 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14171 (p : Pattern) (guard : d4304 p = 1) : d1488 p ≤ (2 : Int) + d4376 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14169 p hg
    simpa only [d4304, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14170 p hg
    simpa only [d4304, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14172 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (2 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14092 p hg
    simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14173 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (2 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14092 p hg
    simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14172 p hg
    simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14174 (p : Pattern) (guard : d4147 p = 1) : d105 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14087 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14173 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14175 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (2 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14176 (p : Pattern) (guard : d4147 p = 1) : d293 p ≤ (2 : Int) + d298 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14175 p hg
    simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6912 p hg
    simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14177 (p : Pattern) (guard : d4147 p = 1) : d1489 p ≤ (2 : Int) + d4382 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1489, d4382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14174 p hg
    simpa only [d1489, d4382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1489, d4382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14176 p hg
    simpa only [d1489, d4382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14178 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14179 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (2 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14180 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (2 : Int) + d298 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14178 p hg
    simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14179 p hg
    simpa only [d132, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14181 (p : Pattern) (guard : d4147 p = 1) : d1133 p ≤ (2 : Int) + d298 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14175 p hg
    simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14180 p hg
    simpa only [d4147, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14182 (p : Pattern) (guard : d4147 p = 1) : d1490 p ≤ (2 : Int) + d4383 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1490, d4383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14181 p hg
    simpa only [d1490, d4383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1490, d4383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14166 p hg
    simpa only [d1490, d4383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14183 (p : Pattern) (guard : d4147 p = 1) : d1491 p ≤ (2 : Int) + d4384 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1491, d4384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14177 p hg
    simpa only [d1491, d4384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1491, d4384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14182 p hg
    simpa only [d1491, d4384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14184 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14185 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d132, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14179 p hg
    simpa only [d132, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14186 (p : Pattern) (guard : d4147 p = 1) : d132 p ≤ (2 : Int) + d109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14184 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14185 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14187 (p : Pattern) (guard : d4147 p = 1) : d1061 p ≤ (2 : Int) + d1140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1061, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14186 p hg
    simpa only [d1061, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1061, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d1061, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14188 (p : Pattern) (guard : d4147 p = 1) : d1062 p ≤ (2 : Int) + d1141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1062, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14187 p hg
    simpa only [d1062, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1062, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d1062, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14189 (p : Pattern) (guard : d4147 p = 1) : d1492 p ≤ (2 : Int) + d4385 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d1492, d4385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14183 p hg
    simpa only [d1492, d4385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d1492, d4385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14188 p hg
    simpa only [d1492, d4385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14190 (p : Pattern) (guard : d0 p = 1) : d1495 p ≤ (2 : Int) + d4385 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14191 (p : Pattern) (guard : d4304 p = 1) : d1496 p ≤ (2 : Int) + d4385 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14189 p hg
    simpa only [d4304, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14190 p hg
    simpa only [d4304, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14192 (p : Pattern) (guard : d4304 p = 1) : d1497 p ≤ (2 : Int) + d5260 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1497, d5260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14171 p hg
    simpa only [d1497, d5260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1497, d5260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14191 p hg
    simpa only [d1497, d5260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14193 (p : Pattern) (guard : d4304 p = 1) : d1498 p ≤ (2 : Int) + d5261 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1498, d5261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14191 p hg
    simpa only [d1498, d5261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1498, d5261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14076 p hg
    simpa only [d1498, d5261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14194 (p : Pattern) (guard : d4304 p = 1) : d1499 p ≤ (2 : Int) + d5262 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1499, d5262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14192 p hg
    simpa only [d1499, d5262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1499, d5262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14193 p hg
    simpa only [d1499, d5262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14195 (p : Pattern) (guard : d4304 p = 1) : d1500 p ≤ (2 : Int) + d5263 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1500, d5263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14153 p hg
    simpa only [d1500, d5263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1500, d5263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14194 p hg
    simpa only [d1500, d5263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14196 (p : Pattern) (guard : d4304 p = 1) : d1501 p ≤ (2 : Int) + d5264 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1501, d5264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14079 p hg
    simpa only [d1501, d5264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1501, d5264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14195 p hg
    simpa only [d1501, d5264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14197 (p : Pattern) (guard : d4304 p = 1) : d1502 p ≤ (2 : Int) + d5265 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1502, d5265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14152 p hg
    simpa only [d1502, d5265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1502, d5265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14196 p hg
    simpa only [d1502, d5265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14198 (p : Pattern) (guard : d4304 p = 1) : d1503 p ≤ (2 : Int) + d5266 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d1503, d5266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14133 p hg
    simpa only [d1503, d5266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d1503, d5266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14197 p hg
    simpa only [d1503, d5266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14199 (p : Pattern) (guard : d1 p = 1) : d267 p ≤ (5 : Int) + d267 p := by
  omega
theorem compare14200 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d318 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14201 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2184 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14200 p hg
    simpa only [d4902, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14202 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d4902, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14203 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2186 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14201 p hg
    simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14204 (p : Pattern) (guard : d4902 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare14205 (p : Pattern) (guard : d4902 p = 1) : d15 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d15, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d15, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d15, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d15, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14206 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d16, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14203 p hg
    simpa only [d16, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d16, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14207 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14208 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2189 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14207 p hg
    simpa only [d4902, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14209 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2190 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14208 p hg
    simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14210 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2191 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d16, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14209 p hg
    simpa only [d16, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d16, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14211 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2192 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14206 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14210 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14212 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14213 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2193 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14212 p hg
    simpa only [d4902, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14214 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2194 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14213 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14215 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d16, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14214 p hg
    simpa only [d16, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d16, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14216 (p : Pattern) (guard : d4902 p = 1) : d18 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d4902, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14217 (p : Pattern) (guard : d4902 p = 1) : d19 p ≤ (0 : Int) + d2197 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d19, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14216 p hg
    simpa only [d19, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d19, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d19, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14218 (p : Pattern) (guard : d4902 p = 1) : d20 p ≤ (0 : Int) + d2198 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d20, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14216 p hg
    simpa only [d20, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d20, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14217 p hg
    simpa only [d20, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14219 (p : Pattern) (guard : d4902 p = 1) : d21 p ≤ (0 : Int) + d2199 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d21, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14215 p hg
    simpa only [d21, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d21, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14218 p hg
    simpa only [d21, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14220 (p : Pattern) (guard : d4902 p = 1) : d22 p ≤ (0 : Int) + d2200 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d22, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14211 p hg
    simpa only [d22, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d22, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14219 p hg
    simpa only [d22, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14221 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d16, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d16, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d16, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14222 (p : Pattern) (guard : d4902 p = 1) : d21 p ≤ (0 : Int) + d2202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d21, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14221 p hg
    simpa only [d21, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d21, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14218 p hg
    simpa only [d21, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14223 (p : Pattern) (guard : d4902 p = 1) : d24 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d4902, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14224 (p : Pattern) (guard : d4902 p = 1) : d25 p ≤ (0 : Int) + d2204 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d25, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14223 p hg
    simpa only [d25, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d25, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d25, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14225 (p : Pattern) (guard : d4902 p = 1) : d26 p ≤ (0 : Int) + d2205 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d26, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14223 p hg
    simpa only [d26, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d26, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14224 p hg
    simpa only [d26, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14226 (p : Pattern) (guard : d4902 p = 1) : d27 p ≤ (0 : Int) + d2206 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d27, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14225 p hg
    simpa only [d27, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d27, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d27, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14227 (p : Pattern) (guard : d4902 p = 1) : d28 p ≤ (0 : Int) + d2207 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d28, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14222 p hg
    simpa only [d28, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d28, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14226 p hg
    simpa only [d28, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14228 (p : Pattern) (guard : d4902 p = 1) : d29 p ≤ (0 : Int) + d2208 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d29, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14220 p hg
    simpa only [d29, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d29, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14227 p hg
    simpa only [d29, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14229 (p : Pattern) (guard : d4902 p = 1) : d31 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d4902, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14230 (p : Pattern) (guard : d4902 p = 1) : d32 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d32, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14229 p hg
    simpa only [d32, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d32, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d32, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14231 (p : Pattern) (guard : d4902 p = 1) : d33 p ≤ (0 : Int) + d2211 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d33, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d33, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d33, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14230 p hg
    simpa only [d33, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14232 (p : Pattern) (guard : d4902 p = 1) : d35 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d4902, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14233 (p : Pattern) (guard : d4902 p = 1) : d36 p ≤ (0 : Int) + d2213 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d36, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14232 p hg
    simpa only [d36, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d36, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d36, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14234 (p : Pattern) (guard : d4902 p = 1) : d37 p ≤ (0 : Int) + d2214 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d37, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d37, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d37, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14233 p hg
    simpa only [d37, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14235 (p : Pattern) (guard : d4902 p = 1) : d38 p ≤ (0 : Int) + d2215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d38, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14231 p hg
    simpa only [d38, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d38, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14234 p hg
    simpa only [d38, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14236 (p : Pattern) (guard : d4902 p = 1) : d40 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d4902, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14237 (p : Pattern) (guard : d4902 p = 1) : d41 p ≤ (0 : Int) + d2217 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d41, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14236 p hg
    simpa only [d41, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d41, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d41, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14238 (p : Pattern) (guard : d4902 p = 1) : d42 p ≤ (0 : Int) + d2218 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d42, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d42, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d42, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14237 p hg
    simpa only [d42, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14239 (p : Pattern) (guard : d4902 p = 1) : d43 p ≤ (0 : Int) + d2219 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d43, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14216 p hg
    simpa only [d43, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d43, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d43, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14240 (p : Pattern) (guard : d4902 p = 1) : d44 p ≤ (0 : Int) + d2220 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d44, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14238 p hg
    simpa only [d44, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d44, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14239 p hg
    simpa only [d44, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14241 (p : Pattern) (guard : d4902 p = 1) : d45 p ≤ (0 : Int) + d2221 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d45, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14235 p hg
    simpa only [d45, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d45, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14240 p hg
    simpa only [d45, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14242 (p : Pattern) (guard : d4902 p = 1) : d46 p ≤ (0 : Int) + d2222 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d46, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d46, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d46, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d46, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14243 (p : Pattern) (guard : d4902 p = 1) : d47 p ≤ (0 : Int) + d2223 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d47, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14242 p hg
    simpa only [d47, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d47, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14239 p hg
    simpa only [d47, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14244 (p : Pattern) (guard : d4902 p = 1) : d48 p ≤ (0 : Int) + d2224 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d48, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14223 p hg
    simpa only [d48, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d48, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d48, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14245 (p : Pattern) (guard : d4902 p = 1) : d49 p ≤ (0 : Int) + d2225 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d49, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14244 p hg
    simpa only [d49, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d49, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d49, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14246 (p : Pattern) (guard : d4902 p = 1) : d50 p ≤ (0 : Int) + d2226 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d50, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14243 p hg
    simpa only [d50, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d50, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14245 p hg
    simpa only [d50, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14247 (p : Pattern) (guard : d4902 p = 1) : d51 p ≤ (0 : Int) + d2227 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d51, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14241 p hg
    simpa only [d51, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d51, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14246 p hg
    simpa only [d51, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14248 (p : Pattern) (guard : d4902 p = 1) : d52 p ≤ (0 : Int) + d2228 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d52, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14228 p hg
    simpa only [d52, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d52, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14247 p hg
    simpa only [d52, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14249 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14250 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2229 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14249 p hg
    simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14251 (p : Pattern) (guard : d4902 p = 1) : d14 p ≤ (0 : Int) + d2230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14250 p hg
    simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14252 (p : Pattern) (guard : d4902 p = 1) : d16 p ≤ (0 : Int) + d2231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d16, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14251 p hg
    simpa only [d16, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d16, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14253 (p : Pattern) (guard : d4902 p = 1) : d53 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d53, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14229 p hg
    simpa only [d53, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d53, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14230 p hg
    simpa only [d53, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14254 (p : Pattern) (guard : d4902 p = 1) : d54 p ≤ (0 : Int) + d2233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d54, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14252 p hg
    simpa only [d54, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d54, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14253 p hg
    simpa only [d54, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14255 (p : Pattern) (guard : d4902 p = 1) : d55 p ≤ (0 : Int) + d2234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d55, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14218 p hg
    simpa only [d55, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d55, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14225 p hg
    simpa only [d55, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14256 (p : Pattern) (guard : d4902 p = 1) : d56 p ≤ (0 : Int) + d2235 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d56, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14254 p hg
    simpa only [d56, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d56, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14255 p hg
    simpa only [d56, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14257 (p : Pattern) (guard : d4902 p = 1) : d58 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14258 (p : Pattern) (guard : d4902 p = 1) : d59 p ≤ (0 : Int) + d2237 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d59, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14257 p hg
    simpa only [d59, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d59, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d59, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14259 (p : Pattern) (guard : d4902 p = 1) : d60 p ≤ (0 : Int) + d2238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d60, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14257 p hg
    simpa only [d60, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d60, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14258 p hg
    simpa only [d60, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14260 (p : Pattern) (guard : d4902 p = 1) : d61 p ≤ (0 : Int) + d2239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d61, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14218 p hg
    simpa only [d61, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d61, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14259 p hg
    simpa only [d61, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14261 (p : Pattern) (guard : d4902 p = 1) : d62 p ≤ (0 : Int) + d2240 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d62, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14236 p hg
    simpa only [d62, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d62, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14237 p hg
    simpa only [d62, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14262 (p : Pattern) (guard : d4902 p = 1) : d63 p ≤ (0 : Int) + d2241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d63, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14261 p hg
    simpa only [d63, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d63, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d63, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14263 (p : Pattern) (guard : d4902 p = 1) : d64 p ≤ (0 : Int) + d2242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d64, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14260 p hg
    simpa only [d64, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d64, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14262 p hg
    simpa only [d64, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14264 (p : Pattern) (guard : d4902 p = 1) : d65 p ≤ (0 : Int) + d2243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d65, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14256 p hg
    simpa only [d65, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d65, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14263 p hg
    simpa only [d65, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14265 (p : Pattern) (guard : d4902 p = 1) : d66 p ≤ (0 : Int) + d2244 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d66, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14229 p hg
    simpa only [d66, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d66, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d66, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14266 (p : Pattern) (guard : d4902 p = 1) : d67 p ≤ (0 : Int) + d2245 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d67, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14234 p hg
    simpa only [d67, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d67, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14265 p hg
    simpa only [d67, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14267 (p : Pattern) (guard : d4902 p = 1) : d68 p ≤ (0 : Int) + d2246 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d68, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14239 p hg
    simpa only [d68, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d68, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14244 p hg
    simpa only [d68, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14268 (p : Pattern) (guard : d4902 p = 1) : d69 p ≤ (0 : Int) + d2247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d69, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14266 p hg
    simpa only [d69, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d69, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14267 p hg
    simpa only [d69, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14269 (p : Pattern) (guard : d4902 p = 1) : d70 p ≤ (0 : Int) + d2248 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d70, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14257 p hg
    simpa only [d70, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d70, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d70, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14270 (p : Pattern) (guard : d4902 p = 1) : d71 p ≤ (0 : Int) + d2249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d71, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14239 p hg
    simpa only [d71, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d71, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14269 p hg
    simpa only [d71, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14271 (p : Pattern) (guard : d4902 p = 1) : d72 p ≤ (0 : Int) + d2250 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d72, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14236 p hg
    simpa only [d72, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d72, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d72, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14272 (p : Pattern) (guard : d4902 p = 1) : d73 p ≤ (0 : Int) + d2251 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d73, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14271 p hg
    simpa only [d73, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d73, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d73, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14273 (p : Pattern) (guard : d4902 p = 1) : d74 p ≤ (0 : Int) + d2252 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d74, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14270 p hg
    simpa only [d74, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d74, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14272 p hg
    simpa only [d74, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14274 (p : Pattern) (guard : d4902 p = 1) : d75 p ≤ (0 : Int) + d2253 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d75, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14268 p hg
    simpa only [d75, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d75, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14273 p hg
    simpa only [d75, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14275 (p : Pattern) (guard : d4902 p = 1) : d76 p ≤ (0 : Int) + d2254 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d76, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14264 p hg
    simpa only [d76, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d76, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14274 p hg
    simpa only [d76, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14276 (p : Pattern) (guard : d4902 p = 1) : d77 p ≤ (0 : Int) + d2255 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d77, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14248 p hg
    simpa only [d77, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d77, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14275 p hg
    simpa only [d77, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14277 (p : Pattern) (guard : d4902 p = 1) : d22 p ≤ (0 : Int) + d2256 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d22, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14221 p hg
    simpa only [d22, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d22, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14222 p hg
    simpa only [d22, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14278 (p : Pattern) (guard : d4902 p = 1) : d29 p ≤ (0 : Int) + d2257 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d29, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14277 p hg
    simpa only [d29, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d29, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14227 p hg
    simpa only [d29, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14279 (p : Pattern) (guard : d4902 p = 1) : d78 p ≤ (0 : Int) + d2258 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d78, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14232 p hg
    simpa only [d78, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d78, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14233 p hg
    simpa only [d78, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
