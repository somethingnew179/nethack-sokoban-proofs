import NetHack.Soko22Hazard87.Compare052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13250 (p : Pattern) (guard : d1386 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13249 p hg
    simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1110 p = 1 := by simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13251 (p : Pattern) (guard : d1387 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1386 p = 1 := by simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13250 p hg
    simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8987 p hg
    simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13252 (p : Pattern) (guard : d1388 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1387 p = 1 := by simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13251 p hg
    simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13253 (p : Pattern) (guard : d160460 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1388 p = 1 := by simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13252 p hg
    simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13254 (p : Pattern) (guard : d160461 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160460 p = 1 := by simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13253 p hg
    simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13255 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1120 p = 1 := by simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8996 p hg
    simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13256 (p : Pattern) (guard : d1392 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13255 p hg
    simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1121 p = 1 := by simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8998 p hg
    simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13257 (p : Pattern) (guard : d1393 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1392 p = 1 := by simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13256 p hg
    simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9007 p hg
    simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13258 (p : Pattern) (guard : d1394 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1393 p = 1 := by simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13257 p hg
    simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13259 (p : Pattern) (guard : d160471 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1394 p = 1 := by simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13258 p hg
    simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13260 (p : Pattern) (guard : d160472 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160471 p = 1 := by simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13259 p hg
    simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13261 (p : Pattern) (guard : d160473 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160461 p = 1 := by simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13254 p hg
    simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160472 p = 1 := by simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13260 p hg
    simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13262 (p : Pattern) (guard : d160474 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160473 p = 1 := by simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13261 p hg
    simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13263 (p : Pattern) (guard : d160475 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160474 p = 1 := by simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13262 p hg
    simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13264 (p : Pattern) (guard : d160476 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160472 p = 1 := by simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13260 p hg
    simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13265 (p : Pattern) (guard : d160477 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160476 p = 1 := by simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13264 p hg
    simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13266 (p : Pattern) (guard : d160478 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160477 p = 1 := by simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13265 p hg
    simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13267 (p : Pattern) (guard : d160479 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160475 p = 1 := by simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13263 p hg
    simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160478 p = 1 := by simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13266 p hg
    simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13268 (p : Pattern) (guard : d160484 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160478 p = 1 := by simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13266 p hg
    simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13269 (p : Pattern) (guard : d160485 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160479 p = 1 := by simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13267 p hg
    simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160484 p = 1 := by simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13268 p hg
    simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13270 (p : Pattern) (guard : d160486 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160485 p = 1 := by simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13269 p hg
    simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13271 (p : Pattern) (guard : d160487 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160486 p = 1 := by simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13270 p hg
    simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13272 (p : Pattern) (guard : d160488 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160487 p = 1 := by simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13271 p hg
    simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13273 (p : Pattern) (guard : d160493 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160484 p = 1 := by simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13268 p hg
    simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13274 (p : Pattern) (guard : d160494 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160493 p = 1 := by simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13273 p hg
    simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13275 (p : Pattern) (guard : d160495 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160494 p = 1 := by simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13274 p hg
    simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13276 (p : Pattern) (guard : d160496 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160495 p = 1 := by simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13275 p hg
    simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13277 (p : Pattern) (guard : d160497 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160488 p = 1 := by simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13272 p hg
    simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160496 p = 1 := by simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13276 p hg
    simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13278 (p : Pattern) (guard : d160498 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160497 p = 1 := by simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13277 p hg
    simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13279 (p : Pattern) (guard : d160499 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160498 p = 1 := by simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13278 p hg
    simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13280 (p : Pattern) (guard : d160500 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160499 p = 1 := by simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13279 p hg
    simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13281 (p : Pattern) (guard : d160514 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160496 p = 1 := by simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13276 p hg
    simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13282 (p : Pattern) (guard : d160515 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160514 p = 1 := by simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13281 p hg
    simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13283 (p : Pattern) (guard : d160516 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160515 p = 1 := by simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13282 p hg
    simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13284 (p : Pattern) (guard : d160517 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160516 p = 1 := by simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13283 p hg
    simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13285 (p : Pattern) (guard : d161112 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160500 p = 1 := by simpa only [d161112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13280 p hg
    simpa only [d161112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160517 p = 1 := by simpa only [d161112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13284 p hg
    simpa only [d161112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13286 (p : Pattern) (guard : d161113 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161112 p = 1 := by simpa only [d161113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13285 p hg
    simpa only [d161113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13287 (p : Pattern) (guard : d161114 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d161113 p = 1 := by simpa only [d161114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13286 p hg
    simpa only [d161114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13288 (p : Pattern) (guard : d161115 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161114 p = 1 := by simpa only [d161115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13287 p hg
    simpa only [d161115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13289 (p : Pattern) (guard : d161116 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161115 p = 1 := by simpa only [d161116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13288 p hg
    simpa only [d161116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13290 (p : Pattern) (guard : d161117 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161117, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161117, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161116 p = 1 := by simpa only [d161117, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13289 p hg
    simpa only [d161117, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13291 (p : Pattern) (guard : d161118 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161117 p = 1 := by simpa only [d161118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13290 p hg
    simpa only [d161118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13292 (p : Pattern) (guard : d161119 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161118 p = 1 := by simpa only [d161119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13291 p hg
    simpa only [d161119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13293 (p : Pattern) (guard : d161120 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161119 p = 1 := by simpa only [d161120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13292 p hg
    simpa only [d161120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13294 (p : Pattern) (guard : d161121 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161120 p = 1 := by simpa only [d161121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13293 p hg
    simpa only [d161121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13295 (p : Pattern) (guard : d161122 p = 1) : d47865 p ≤ (-2 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161121 p = 1 := by simpa only [d161122, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13294 p hg
    simpa only [d161122, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161122, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12901 p hg
    simpa only [d161122, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13296 (p : Pattern) (guard : d161123 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d161111 p = 1 := by simpa only [d161123, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13248 p hg
    simpa only [d161123, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161122 p = 1 := by simpa only [d161123, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13295 p hg
    simpa only [d161123, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13297 (p : Pattern) (guard : d161124 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161123 p = 1 := by simpa only [d161124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13296 p hg
    simpa only [d161124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13298 (p : Pattern) (guard : d161125 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161124 p = 1 := by simpa only [d161125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13297 p hg
    simpa only [d161125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13299 (p : Pattern) (guard : d161126 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161125 p = 1 := by simpa only [d161126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13298 p hg
    simpa only [d161126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13300 (p : Pattern) (guard : d161127 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161126 p = 1 := by simpa only [d161127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13299 p hg
    simpa only [d161127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13301 (p : Pattern) (guard : d161128 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161127 p = 1 := by simpa only [d161128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13300 p hg
    simpa only [d161128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13302 (p : Pattern) (guard : d161129 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161128 p = 1 := by simpa only [d161129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13301 p hg
    simpa only [d161129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13303 (p : Pattern) (guard : d161130 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161129 p = 1 := by simpa only [d161130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13302 p hg
    simpa only [d161130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13304 (p : Pattern) (guard : d161131 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161130 p = 1 := by simpa only [d161131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13303 p hg
    simpa only [d161131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13305 (p : Pattern) (guard : d161132 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d161103 p = 1 := by simpa only [d161132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13155 p hg
    simpa only [d161132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161131 p = 1 := by simpa only [d161132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13304 p hg
    simpa only [d161132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13306 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9135 p hg
    simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13307 (p : Pattern) (guard : d1573 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13306 p hg
    simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13308 (p : Pattern) (guard : d160539 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13307 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13309 (p : Pattern) (guard : d160540 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160539 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13308 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13310 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9147 p hg
    simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13311 (p : Pattern) (guard : d1585 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13310 p hg
    simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13312 (p : Pattern) (guard : d160541 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13311 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13313 (p : Pattern) (guard : d160542 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160541 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13312 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13314 (p : Pattern) (guard : d160543 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160540 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13309 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160542 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13313 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13315 (p : Pattern) (guard : d160544 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160543 p = 1 := by simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13314 p hg
    simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13316 (p : Pattern) (guard : d160545 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160544 p = 1 := by simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13315 p hg
    simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13317 (p : Pattern) (guard : d160546 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160542 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13313 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13318 (p : Pattern) (guard : d160547 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160546 p = 1 := by simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13317 p hg
    simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13319 (p : Pattern) (guard : d160548 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160547 p = 1 := by simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13318 p hg
    simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13320 (p : Pattern) (guard : d160549 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160545 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13316 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160548 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13319 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13321 (p : Pattern) (guard : d160550 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160548 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13319 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13322 (p : Pattern) (guard : d160551 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160549 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13320 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160550 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13321 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13323 (p : Pattern) (guard : d160552 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160551 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13322 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13324 (p : Pattern) (guard : d160553 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160552 p = 1 := by simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13323 p hg
    simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13325 (p : Pattern) (guard : d160554 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160553 p = 1 := by simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13324 p hg
    simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13326 (p : Pattern) (guard : d160555 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160550 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13321 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13327 (p : Pattern) (guard : d160556 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160555 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13326 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13328 (p : Pattern) (guard : d160557 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160556 p = 1 := by simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13327 p hg
    simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13329 (p : Pattern) (guard : d160558 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160557 p = 1 := by simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13328 p hg
    simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13330 (p : Pattern) (guard : d160559 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160554 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13325 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160558 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13329 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13331 (p : Pattern) (guard : d160560 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160559 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13330 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13332 (p : Pattern) (guard : d160561 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160560 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13331 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13333 (p : Pattern) (guard : d160562 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160561 p = 1 := by simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13332 p hg
    simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13334 (p : Pattern) (guard : d160563 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160558 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13329 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13335 (p : Pattern) (guard : d160564 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160563 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13334 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13336 (p : Pattern) (guard : d160565 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160564 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13335 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13337 (p : Pattern) (guard : d160566 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160565 p = 1 := by simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13336 p hg
    simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13338 (p : Pattern) (guard : d160567 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160562 p = 1 := by simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13333 p hg
    simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160566 p = 1 := by simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13337 p hg
    simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13339 (p : Pattern) (guard : d160568 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160567 p = 1 := by simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13338 p hg
    simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13340 (p : Pattern) (guard : d160569 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160568 p = 1 := by simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13339 p hg
    simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13341 (p : Pattern) (guard : d160570 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160569 p = 1 := by simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13340 p hg
    simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13342 (p : Pattern) (guard : d160571 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160570 p = 1 := by simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13341 p hg
    simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13343 (p : Pattern) (guard : d160572 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160571 p = 1 := by simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13342 p hg
    simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13344 (p : Pattern) (guard : d160575 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160561 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13332 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13345 (p : Pattern) (guard : d160576 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160565 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13336 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13346 (p : Pattern) (guard : d160577 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160575 p = 1 := by simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13344 p hg
    simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160576 p = 1 := by simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13345 p hg
    simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13347 (p : Pattern) (guard : d160578 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160577 p = 1 := by simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13346 p hg
    simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13348 (p : Pattern) (guard : d160579 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160578 p = 1 := by simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13347 p hg
    simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13349 (p : Pattern) (guard : d160580 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160579 p = 1 := by simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13348 p hg
    simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13350 (p : Pattern) (guard : d160581 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160580 p = 1 := by simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13349 p hg
    simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13351 (p : Pattern) (guard : d160582 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160571 p = 1 := by simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13342 p hg
    simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160581 p = 1 := by simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13350 p hg
    simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13352 (p : Pattern) (guard : d160583 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160572 p = 1 := by simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13343 p hg
    simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160582 p = 1 := by simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13351 p hg
    simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13353 (p : Pattern) (guard : d160584 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160583 p = 1 := by simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13352 p hg
    simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13354 (p : Pattern) (guard : d161133 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160584 p = 1 := by simpa only [d161133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13353 p hg
    simpa only [d161133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13355 (p : Pattern) (guard : d161134 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161133 p = 1 := by simpa only [d161134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13354 p hg
    simpa only [d161134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13356 (p : Pattern) (guard : d1572 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9265 p hg
    simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13357 (p : Pattern) (guard : d1573 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13356 p hg
    simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13358 (p : Pattern) (guard : d160539 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13357 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13359 (p : Pattern) (guard : d160540 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160539 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13358 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13360 (p : Pattern) (guard : d1584 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9277 p hg
    simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13361 (p : Pattern) (guard : d1585 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13360 p hg
    simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13362 (p : Pattern) (guard : d160541 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13361 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13363 (p : Pattern) (guard : d160542 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160541 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13362 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13364 (p : Pattern) (guard : d160543 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160540 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13359 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160542 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13363 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13365 (p : Pattern) (guard : d160544 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160543 p = 1 := by simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13364 p hg
    simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13366 (p : Pattern) (guard : d160545 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160544 p = 1 := by simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13365 p hg
    simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13367 (p : Pattern) (guard : d160546 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160542 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13363 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13368 (p : Pattern) (guard : d160547 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160546 p = 1 := by simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13367 p hg
    simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13369 (p : Pattern) (guard : d160548 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160547 p = 1 := by simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13368 p hg
    simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13370 (p : Pattern) (guard : d160549 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160545 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13366 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160548 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13369 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13371 (p : Pattern) (guard : d160550 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160548 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13369 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13372 (p : Pattern) (guard : d160551 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160549 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13370 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160550 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13371 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13373 (p : Pattern) (guard : d160552 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160551 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13372 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13374 (p : Pattern) (guard : d160553 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160552 p = 1 := by simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13373 p hg
    simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13375 (p : Pattern) (guard : d160554 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160553 p = 1 := by simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13374 p hg
    simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13376 (p : Pattern) (guard : d160555 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160550 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13371 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13377 (p : Pattern) (guard : d160556 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160555 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13376 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13378 (p : Pattern) (guard : d160557 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160556 p = 1 := by simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13377 p hg
    simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13379 (p : Pattern) (guard : d160558 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160557 p = 1 := by simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13378 p hg
    simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13380 (p : Pattern) (guard : d160559 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160554 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13375 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160558 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13379 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13381 (p : Pattern) (guard : d160560 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160559 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13380 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13382 (p : Pattern) (guard : d160561 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160560 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13381 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13383 (p : Pattern) (guard : d160575 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160561 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13382 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13384 (p : Pattern) (guard : d160563 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160558 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13379 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13385 (p : Pattern) (guard : d160564 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160563 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13384 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13386 (p : Pattern) (guard : d160565 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160564 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13385 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13387 (p : Pattern) (guard : d160576 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160565 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13386 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13388 (p : Pattern) (guard : d160577 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160575 p = 1 := by simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13383 p hg
    simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160576 p = 1 := by simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13387 p hg
    simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13389 (p : Pattern) (guard : d160578 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160577 p = 1 := by simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13388 p hg
    simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13390 (p : Pattern) (guard : d160579 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160578 p = 1 := by simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13389 p hg
    simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13391 (p : Pattern) (guard : d160580 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160579 p = 1 := by simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13390 p hg
    simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13392 (p : Pattern) (guard : d160581 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160580 p = 1 := by simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13391 p hg
    simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13393 (p : Pattern) (guard : d161135 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161135, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161135, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160581 p = 1 := by simpa only [d161135, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13392 p hg
    simpa only [d161135, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13394 (p : Pattern) (guard : d161136 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161135 p = 1 := by simpa only [d161136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13393 p hg
    simpa only [d161136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13395 (p : Pattern) (guard : d161137 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161136 p = 1 := by simpa only [d161137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13394 p hg
    simpa only [d161137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13396 (p : Pattern) (guard : d161138 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161137 p = 1 := by simpa only [d161138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13395 p hg
    simpa only [d161138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13397 (p : Pattern) (guard : d161139 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161138 p = 1 := by simpa only [d161139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13396 p hg
    simpa only [d161139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13398 (p : Pattern) (guard : d161140 p = 1) : d47768 p ≤ (-2 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161134 p = 1 := by simpa only [d161140, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13355 p hg
    simpa only [d161140, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161139 p = 1 := by simpa only [d161140, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13397 p hg
    simpa only [d161140, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13399 (p : Pattern) (guard : d1862 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1569 p = 1 := by simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9432 p hg
    simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13400 (p : Pattern) (guard : d1863 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1862 p = 1 := by simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13399 p hg
    simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1570 p = 1 := by simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9434 p hg
    simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13401 (p : Pattern) (guard : d1864 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1863 p = 1 := by simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13400 p hg
    simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9448 p hg
    simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13402 (p : Pattern) (guard : d1865 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1864 p = 1 := by simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13401 p hg
    simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13403 (p : Pattern) (guard : d160684 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1865 p = 1 := by simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13402 p hg
    simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13404 (p : Pattern) (guard : d160685 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160684 p = 1 := by simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13403 p hg
    simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13405 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1581 p = 1 := by simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9458 p hg
    simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13406 (p : Pattern) (guard : d1869 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13405 p hg
    simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1582 p = 1 := by simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13407 (p : Pattern) (guard : d1870 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1869 p = 1 := by simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13406 p hg
    simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9470 p hg
    simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13408 (p : Pattern) (guard : d1871 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1870 p = 1 := by simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13407 p hg
    simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13409 (p : Pattern) (guard : d160695 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1871 p = 1 := by simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13408 p hg
    simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13410 (p : Pattern) (guard : d160696 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160695 p = 1 := by simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13409 p hg
    simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13411 (p : Pattern) (guard : d160697 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160685 p = 1 := by simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13404 p hg
    simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160696 p = 1 := by simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13410 p hg
    simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13412 (p : Pattern) (guard : d160698 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160697 p = 1 := by simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13411 p hg
    simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13413 (p : Pattern) (guard : d160699 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160698 p = 1 := by simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13412 p hg
    simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13414 (p : Pattern) (guard : d160700 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160696 p = 1 := by simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13410 p hg
    simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13415 (p : Pattern) (guard : d160701 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160700 p = 1 := by simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13414 p hg
    simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13416 (p : Pattern) (guard : d160702 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160701 p = 1 := by simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13415 p hg
    simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13417 (p : Pattern) (guard : d160703 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160699 p = 1 := by simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13413 p hg
    simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160702 p = 1 := by simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13416 p hg
    simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13418 (p : Pattern) (guard : d160708 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160702 p = 1 := by simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13416 p hg
    simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13419 (p : Pattern) (guard : d160709 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160703 p = 1 := by simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13417 p hg
    simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160708 p = 1 := by simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13418 p hg
    simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13420 (p : Pattern) (guard : d160710 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160709 p = 1 := by simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13419 p hg
    simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13421 (p : Pattern) (guard : d160711 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160710 p = 1 := by simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13420 p hg
    simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13422 (p : Pattern) (guard : d160712 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160711 p = 1 := by simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13421 p hg
    simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13423 (p : Pattern) (guard : d160717 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160708 p = 1 := by simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13418 p hg
    simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13424 (p : Pattern) (guard : d160718 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160717 p = 1 := by simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13423 p hg
    simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13425 (p : Pattern) (guard : d160719 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160718 p = 1 := by simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13424 p hg
    simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13426 (p : Pattern) (guard : d160720 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160719 p = 1 := by simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13425 p hg
    simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13427 (p : Pattern) (guard : d160721 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160712 p = 1 := by simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13422 p hg
    simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160720 p = 1 := by simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13426 p hg
    simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13428 (p : Pattern) (guard : d160722 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160721 p = 1 := by simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13427 p hg
    simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13429 (p : Pattern) (guard : d160723 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160722 p = 1 := by simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13428 p hg
    simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13430 (p : Pattern) (guard : d160724 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160723 p = 1 := by simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13429 p hg
    simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13431 (p : Pattern) (guard : d160738 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160720 p = 1 := by simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13426 p hg
    simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13432 (p : Pattern) (guard : d160739 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160738 p = 1 := by simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13431 p hg
    simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13433 (p : Pattern) (guard : d160740 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160739 p = 1 := by simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13432 p hg
    simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13434 (p : Pattern) (guard : d160741 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160740 p = 1 := by simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13433 p hg
    simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13435 (p : Pattern) (guard : d161141 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160724 p = 1 := by simpa only [d161141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13430 p hg
    simpa only [d161141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160741 p = 1 := by simpa only [d161141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13434 p hg
    simpa only [d161141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13436 (p : Pattern) (guard : d161142 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161141 p = 1 := by simpa only [d161142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13435 p hg
    simpa only [d161142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13437 (p : Pattern) (guard : d161143 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d161142 p = 1 := by simpa only [d161143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13436 p hg
    simpa only [d161143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13438 (p : Pattern) (guard : d161144 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161143 p = 1 := by simpa only [d161144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13437 p hg
    simpa only [d161144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13439 (p : Pattern) (guard : d161145 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161144 p = 1 := by simpa only [d161145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13438 p hg
    simpa only [d161145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13440 (p : Pattern) (guard : d161146 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161146, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161146, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161145 p = 1 := by simpa only [d161146, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13439 p hg
    simpa only [d161146, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13441 (p : Pattern) (guard : d161147 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161146 p = 1 := by simpa only [d161147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13440 p hg
    simpa only [d161147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13442 (p : Pattern) (guard : d161148 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161147 p = 1 := by simpa only [d161148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13441 p hg
    simpa only [d161148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13443 (p : Pattern) (guard : d161149 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161148 p = 1 := by simpa only [d161149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13442 p hg
    simpa only [d161149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13444 (p : Pattern) (guard : d161150 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161149 p = 1 := by simpa only [d161150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13443 p hg
    simpa only [d161150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13445 (p : Pattern) (guard : d161151 p = 1) : d47865 p ≤ (-2 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161150 p = 1 := by simpa only [d161151, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13444 p hg
    simpa only [d161151, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161151, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12901 p hg
    simpa only [d161151, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13446 (p : Pattern) (guard : d161152 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d161140 p = 1 := by simpa only [d161152, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13398 p hg
    simpa only [d161152, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161151 p = 1 := by simpa only [d161152, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13445 p hg
    simpa only [d161152, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13447 (p : Pattern) (guard : d161153 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161152 p = 1 := by simpa only [d161153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13446 p hg
    simpa only [d161153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13448 (p : Pattern) (guard : d161154 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161153 p = 1 := by simpa only [d161154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13447 p hg
    simpa only [d161154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13449 (p : Pattern) (guard : d161155 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161154 p = 1 := by simpa only [d161155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13448 p hg
    simpa only [d161155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13450 (p : Pattern) (guard : d161156 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161155 p = 1 := by simpa only [d161156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13449 p hg
    simpa only [d161156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13451 (p : Pattern) (guard : d161157 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161156 p = 1 := by simpa only [d161157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13450 p hg
    simpa only [d161157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13452 (p : Pattern) (guard : d161158 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161157 p = 1 := by simpa only [d161158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13451 p hg
    simpa only [d161158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13453 (p : Pattern) (guard : d161159 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161158 p = 1 := by simpa only [d161159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13452 p hg
    simpa only [d161159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13454 (p : Pattern) (guard : d161160 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161159 p = 1 := by simpa only [d161160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13453 p hg
    simpa only [d161160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13455 (p : Pattern) (guard : d161161 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161160 p = 1 := by simpa only [d161161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13454 p hg
    simpa only [d161161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13456 (p : Pattern) (guard : d161162 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d161132 p = 1 := by simpa only [d161162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13305 p hg
    simpa only [d161162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161161 p = 1 := by simpa only [d161162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13455 p hg
    simpa only [d161162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13457 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13458 (p : Pattern) (guard : d2056 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13457 p hg
    simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13459 (p : Pattern) (guard : d160764 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13458 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13460 (p : Pattern) (guard : d160765 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160764 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13459 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13461 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9609 p hg
    simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13462 (p : Pattern) (guard : d2068 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13461 p hg
    simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13463 (p : Pattern) (guard : d160766 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13462 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13464 (p : Pattern) (guard : d160767 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160766 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13463 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13465 (p : Pattern) (guard : d160768 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160765 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13460 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160767 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13464 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13466 (p : Pattern) (guard : d160769 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160768 p = 1 := by simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13465 p hg
    simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13467 (p : Pattern) (guard : d160770 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160769 p = 1 := by simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13466 p hg
    simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13468 (p : Pattern) (guard : d160771 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160767 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13464 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13469 (p : Pattern) (guard : d160772 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160771 p = 1 := by simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13468 p hg
    simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13470 (p : Pattern) (guard : d160773 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160772 p = 1 := by simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13469 p hg
    simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13471 (p : Pattern) (guard : d160774 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160770 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13467 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160773 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13470 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13472 (p : Pattern) (guard : d160775 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160773 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13470 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13473 (p : Pattern) (guard : d160776 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160774 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13471 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160775 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13472 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13474 (p : Pattern) (guard : d160777 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160776 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13473 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13475 (p : Pattern) (guard : d160778 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160777 p = 1 := by simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13474 p hg
    simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13476 (p : Pattern) (guard : d160779 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160778 p = 1 := by simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13475 p hg
    simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13477 (p : Pattern) (guard : d160780 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160775 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13472 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13478 (p : Pattern) (guard : d160781 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160780 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13477 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13479 (p : Pattern) (guard : d160782 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160781 p = 1 := by simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13478 p hg
    simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13480 (p : Pattern) (guard : d160783 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160782 p = 1 := by simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13479 p hg
    simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13481 (p : Pattern) (guard : d160784 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160779 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13476 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160783 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13480 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13482 (p : Pattern) (guard : d160785 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160784 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13481 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13483 (p : Pattern) (guard : d160786 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160785 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13482 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13484 (p : Pattern) (guard : d160787 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160786 p = 1 := by simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13483 p hg
    simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13485 (p : Pattern) (guard : d160788 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160783 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13480 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13486 (p : Pattern) (guard : d160789 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160788 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13485 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13487 (p : Pattern) (guard : d160790 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160789 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13486 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13488 (p : Pattern) (guard : d160791 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160790 p = 1 := by simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13487 p hg
    simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13489 (p : Pattern) (guard : d160792 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160787 p = 1 := by simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13484 p hg
    simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160791 p = 1 := by simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13488 p hg
    simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13490 (p : Pattern) (guard : d160793 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160792 p = 1 := by simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13489 p hg
    simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13491 (p : Pattern) (guard : d160794 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160793 p = 1 := by simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13490 p hg
    simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13492 (p : Pattern) (guard : d160795 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160794 p = 1 := by simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13491 p hg
    simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13493 (p : Pattern) (guard : d160796 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160795 p = 1 := by simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13492 p hg
    simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13494 (p : Pattern) (guard : d160797 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160796 p = 1 := by simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13493 p hg
    simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13495 (p : Pattern) (guard : d160800 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160786 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13483 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13496 (p : Pattern) (guard : d160801 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160790 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13487 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13497 (p : Pattern) (guard : d160802 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160800 p = 1 := by simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13495 p hg
    simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160801 p = 1 := by simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13496 p hg
    simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13498 (p : Pattern) (guard : d160803 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160802 p = 1 := by simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13497 p hg
    simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13499 (p : Pattern) (guard : d160804 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160803 p = 1 := by simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13498 p hg
    simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
