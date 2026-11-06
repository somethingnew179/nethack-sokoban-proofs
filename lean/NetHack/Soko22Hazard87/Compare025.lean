import NetHack.Soko22Hazard87.Compare024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6250 (p : Pattern) (guard : d1381 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1380 p = 1 := by simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6248 p hg
    simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1100 p = 1 := by simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6249 p hg
    simpa only [d1381, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6251 (p : Pattern) (guard : d1093 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6229 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4543 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6252 (p : Pattern) (guard : d1094 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6251 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6253 (p : Pattern) (guard : d1095 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6252 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6254 (p : Pattern) (guard : d1096 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6232 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6253 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6255 (p : Pattern) (guard : d1097 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6254 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5300 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6256 (p : Pattern) (guard : d1098 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6255 p hg
    simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1098, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6257 (p : Pattern) (guard : d1099 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6235 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6258 (p : Pattern) (guard : d1100 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6257 p hg
    simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1100, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6259 (p : Pattern) (guard : d1101 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6258 p hg
    simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1101, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6260 (p : Pattern) (guard : d1382 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1381 p = 1 := by simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6250 p hg
    simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d1382, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6261 (p : Pattern) (guard : d1383 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1382 p = 1 := by simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6260 p hg
    simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1383, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6262 (p : Pattern) (guard : d1384 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1379 p = 1 := by simpa only [d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6240 p hg
    simpa only [d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1383 p = 1 := by simpa only [d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6263 (p : Pattern) (guard : d1104 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4726 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6264 (p : Pattern) (guard : d1105 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6263 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6265 (p : Pattern) (guard : d1106 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6264 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6266 (p : Pattern) (guard : d1107 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6265 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6267 (p : Pattern) (guard : d1108 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6266 p hg
    simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1108, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6268 (p : Pattern) (guard : d1109 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6246 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6267 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6269 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1109 p = 1 := by simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6268 p hg
    simpa only [d1385, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6270 (p : Pattern) (guard : d1110 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1110, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6271 (p : Pattern) (guard : d1386 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6269 p hg
    simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1110 p = 1 := by simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d1386, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6272 (p : Pattern) (guard : d1104 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4742 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6273 (p : Pattern) (guard : d1105 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6272 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6274 (p : Pattern) (guard : d1106 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6253 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6273 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6275 (p : Pattern) (guard : d1107 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6274 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6276 (p : Pattern) (guard : d1108 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6275 p hg
    simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1108, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6277 (p : Pattern) (guard : d1109 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6278 (p : Pattern) (guard : d1110 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6277 p hg
    simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1110, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6279 (p : Pattern) (guard : d1111 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6278 p hg
    simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1111, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6280 (p : Pattern) (guard : d1387 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1386 p = 1 := by simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6271 p hg
    simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6279 p hg
    simpa only [d1387, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6281 (p : Pattern) (guard : d1388 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1387 p = 1 := by simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6280 p hg
    simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1388, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6282 (p : Pattern) (guard : d1389 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1383 p = 1 := by simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1388 p = 1 := by simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6281 p hg
    simpa only [d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6283 (p : Pattern) (guard : d1390 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1384 p = 1 := by simpa only [d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6262 p hg
    simpa only [d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1389 p = 1 := by simpa only [d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6282 p hg
    simpa only [d1390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6284 (p : Pattern) (guard : d1115 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6285 (p : Pattern) (guard : d1116 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6286 (p : Pattern) (guard : d1117 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6285 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4528 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6287 (p : Pattern) (guard : d1118 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6286 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6288 (p : Pattern) (guard : d1119 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6287 p hg
    simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1119, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6289 (p : Pattern) (guard : d1120 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6267 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6288 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6290 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1120 p = 1 := by simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6289 p hg
    simpa only [d1391, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6291 (p : Pattern) (guard : d1121 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1121, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6292 (p : Pattern) (guard : d1392 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6290 p hg
    simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1121 p = 1 := by simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d1392, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6293 (p : Pattern) (guard : d1115 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6294 (p : Pattern) (guard : d1116 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6295 (p : Pattern) (guard : d1117 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6296 (p : Pattern) (guard : d1118 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6295 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4547 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6297 (p : Pattern) (guard : d1119 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6296 p hg
    simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1119, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6298 (p : Pattern) (guard : d1120 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6297 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6299 (p : Pattern) (guard : d1121 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6298 p hg
    simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1121, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6300 (p : Pattern) (guard : d1122 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6299 p hg
    simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1122, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6301 (p : Pattern) (guard : d1393 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1392 p = 1 := by simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6292 p hg
    simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6300 p hg
    simpa only [d1393, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6302 (p : Pattern) (guard : d1394 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1393 p = 1 := by simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6301 p hg
    simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1394, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6303 (p : Pattern) (guard : d1395 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1388 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6281 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1394 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6302 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6304 (p : Pattern) (guard : d1396 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1389 p = 1 := by simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6282 p hg
    simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1395 p = 1 := by simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6305 (p : Pattern) (guard : d1397 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1390 p = 1 := by simpa only [d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6283 p hg
    simpa only [d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1396 p = 1 := by simpa only [d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6304 p hg
    simpa only [d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6306 (p : Pattern) (guard : d1398 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1398, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d1398, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1397 p = 1 := by simpa only [d1398, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6305 p hg
    simpa only [d1398, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6307 (p : Pattern) (guard : d1399 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1399, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d1399, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1398 p = 1 := by simpa only [d1399, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6306 p hg
    simpa only [d1399, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6308 (p : Pattern) (guard : d1400 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1394 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6302 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6309 (p : Pattern) (guard : d1401 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1395 p = 1 := by simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1400 p = 1 := by simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6310 (p : Pattern) (guard : d1402 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1396 p = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6304 p hg
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1401 p = 1 := by simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6309 p hg
    simpa only [d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6311 (p : Pattern) (guard : d1403 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1402 p = 1 := by simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6310 p hg
    simpa only [d1403, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6312 (p : Pattern) (guard : d1404 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1403 p = 1 := by simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6311 p hg
    simpa only [d1404, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6313 (p : Pattern) (guard : d1405 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1399 p = 1 := by simpa only [d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6307 p hg
    simpa only [d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1404 p = 1 := by simpa only [d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6312 p hg
    simpa only [d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6314 (p : Pattern) (guard : d1132 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6285 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6315 (p : Pattern) (guard : d1133 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6314 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6316 (p : Pattern) (guard : d1134 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1134, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6317 (p : Pattern) (guard : d1135 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6316 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6318 (p : Pattern) (guard : d1406 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1135 p = 1 := by simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6317 p hg
    simpa only [d1406, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6319 (p : Pattern) (guard : d1136 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5850 p hg
    simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1136, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6320 (p : Pattern) (guard : d1407 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1406 p = 1 := by simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6318 p hg
    simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1136 p = 1 := by simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6319 p hg
    simpa only [d1407, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6321 (p : Pattern) (guard : d1132 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6322 (p : Pattern) (guard : d1133 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6321 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6323 (p : Pattern) (guard : d1134 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6322 p hg
    simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1134, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6324 (p : Pattern) (guard : d1135 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6323 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6325 (p : Pattern) (guard : d1136 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6324 p hg
    simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1136, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6326 (p : Pattern) (guard : d1137 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6325 p hg
    simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1137, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6327 (p : Pattern) (guard : d1408 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1407 p = 1 := by simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6320 p hg
    simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6326 p hg
    simpa only [d1408, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6328 (p : Pattern) (guard : d1409 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1408 p = 1 := by simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6327 p hg
    simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1409, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6329 (p : Pattern) (guard : d1410 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1409 p = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6328 p hg
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6330 (p : Pattern) (guard : d1411 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1400 p = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1410 p = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6329 p hg
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6331 (p : Pattern) (guard : d1412 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1401 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6309 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1411 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6330 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6332 (p : Pattern) (guard : d1413 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6331 p hg
    simpa only [d1413, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6333 (p : Pattern) (guard : d1414 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1413 p = 1 := by simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6332 p hg
    simpa only [d1414, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6334 (p : Pattern) (guard : d1415 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1404 p = 1 := by simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6312 p hg
    simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1414 p = 1 := by simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6335 (p : Pattern) (guard : d1416 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1405 p = 1 := by simpa only [d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6313 p hg
    simpa only [d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1415 p = 1 := by simpa only [d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6334 p hg
    simpa only [d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6336 (p : Pattern) (guard : d1417 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1416 p = 1 := by simpa only [d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6335 p hg
    simpa only [d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6337 (p : Pattern) (guard : d1418 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1417 p = 1 := by simpa only [d1418, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6336 p hg
    simpa only [d1418, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1418, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d1418, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6338 (p : Pattern) (guard : d1419 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1419, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1419, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1418 p = 1 := by simpa only [d1419, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6337 p hg
    simpa only [d1419, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6339 (p : Pattern) (guard : d7000 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1404 p = 1 := by simpa only [d7000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6312 p hg
    simpa only [d7000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d7000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6340 (p : Pattern) (guard : d6349 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1395 p = 1 := by simpa only [d6349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d6349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6341 (p : Pattern) (guard : d5010 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4524 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6342 (p : Pattern) (guard : d5011 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6341 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6343 (p : Pattern) (guard : d5012 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6342 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6344 (p : Pattern) (guard : d5013 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6343 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6345 (p : Pattern) (guard : d5014 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6344 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6346 (p : Pattern) (guard : d5015 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6345 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6347 (p : Pattern) (guard : d5016 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6346 p hg
    simpa only [d5016, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d5016, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6348 (p : Pattern) (guard : d5017 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6347 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6288 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6349 (p : Pattern) (guard : d6350 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6350, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d6350, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5017 p = 1 := by simpa only [d6350, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6348 p hg
    simpa only [d6350, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6350 (p : Pattern) (guard : d5018 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5948 p hg
    simpa only [d5018, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d5018, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6351 (p : Pattern) (guard : d6351 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6350 p = 1 := by simpa only [d6351, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d6351, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5018 p = 1 := by simpa only [d6351, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6350 p hg
    simpa only [d6351, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6352 (p : Pattern) (guard : d5010 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4542 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6353 (p : Pattern) (guard : d5011 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6352 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4543 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6354 (p : Pattern) (guard : d5012 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6353 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6355 (p : Pattern) (guard : d5013 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6356 (p : Pattern) (guard : d5014 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6253 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6355 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6357 (p : Pattern) (guard : d5015 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6356 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6358 (p : Pattern) (guard : d5016 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6357 p hg
    simpa only [d5016, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d5016, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6359 (p : Pattern) (guard : d5017 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6358 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6297 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6360 (p : Pattern) (guard : d5018 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6359 p hg
    simpa only [d5018, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5018, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6361 (p : Pattern) (guard : d5019 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d5019, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5019, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6362 (p : Pattern) (guard : d6352 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6351 p = 1 := by simpa only [d6352, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6351 p hg
    simpa only [d6352, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d6352, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d6352, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6363 (p : Pattern) (guard : d6353 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6352 p = 1 := by simpa only [d6353, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6362 p hg
    simpa only [d6353, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6353, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d6353, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6364 (p : Pattern) (guard : d6354 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6353 p = 1 := by simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6365 (p : Pattern) (guard : d6355 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6354 p = 1 := by simpa only [d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6364 p hg
    simpa only [d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6366 (p : Pattern) (guard : d6356 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d6349 p = 1 := by simpa only [d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6340 p hg
    simpa only [d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6355 p = 1 := by simpa only [d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6365 p hg
    simpa only [d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6367 (p : Pattern) (guard : d6357 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6357, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d6357, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6356 p = 1 := by simpa only [d6357, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6366 p hg
    simpa only [d6357, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6368 (p : Pattern) (guard : d6358 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6358, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d6358, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6357 p = 1 := by simpa only [d6358, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d6358, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6369 (p : Pattern) (guard : d6359 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d6358 p = 1 := by simpa only [d6359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6368 p hg
    simpa only [d6359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6370 (p : Pattern) (guard : d7001 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d7000 p = 1 := by simpa only [d7001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d7001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6359 p = 1 := by simpa only [d7001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6369 p hg
    simpa only [d7001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6371 (p : Pattern) (guard : d7002 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d7001 p = 1 := by simpa only [d7002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d7002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d7002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6372 (p : Pattern) (guard : d7003 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d7002 p = 1 := by simpa only [d7003, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6371 p hg
    simpa only [d7003, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7003, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d7003, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6373 (p : Pattern) (guard : d7004 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7004, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d7004, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7003 p = 1 := by simpa only [d7004, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6372 p hg
    simpa only [d7004, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6374 (p : Pattern) (guard : d7005 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1419 p = 1 := by simpa only [d7005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6338 p hg
    simpa only [d7005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7004 p = 1 := by simpa only [d7005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6373 p hg
    simpa only [d7005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6375 (p : Pattern) (guard : d7006 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7005 p = 1 := by simpa only [d7006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6374 p hg
    simpa only [d7006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6376 (p : Pattern) (guard : d7007 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7006 p = 1 := by simpa only [d7007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d7007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6377 (p : Pattern) (guard : d7008 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7007 p = 1 := by simpa only [d7008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d7008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6378 (p : Pattern) (guard : d6360 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1415 p = 1 := by simpa only [d6360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6334 p hg
    simpa only [d6360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6359 p = 1 := by simpa only [d6360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6369 p hg
    simpa only [d6360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6379 (p : Pattern) (guard : d6361 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6360 p = 1 := by simpa only [d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6380 (p : Pattern) (guard : d6362 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6361 p = 1 := by simpa only [d6362, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d6362, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6362, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6362, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6381 (p : Pattern) (guard : d6363 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6363, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6363, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6362 p = 1 := by simpa only [d6363, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6380 p hg
    simpa only [d6363, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6382 (p : Pattern) (guard : d1420 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1414 p = 1 := by simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6383 (p : Pattern) (guard : d1429 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1420 p = 1 := by simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6384 (p : Pattern) (guard : d1430 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1429 p = 1 := by simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6385 (p : Pattern) (guard : d1431 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1430 p = 1 := by simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6384 p hg
    simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d1431, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6386 (p : Pattern) (guard : d1432 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1431 p = 1 := by simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6385 p hg
    simpa only [d1432, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6387 (p : Pattern) (guard : d7009 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d6363 p = 1 := by simpa only [d7009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d7009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1432 p = 1 := by simpa only [d7009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d7009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6388 (p : Pattern) (guard : d7010 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7009 p = 1 := by simpa only [d7010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6387 p hg
    simpa only [d7010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6389 (p : Pattern) (guard : d7011 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7010 p = 1 := by simpa only [d7011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d7011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6390 (p : Pattern) (guard : d7012 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7011 p = 1 := by simpa only [d7012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d7012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6391 (p : Pattern) (guard : d7013 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7008 p = 1 := by simpa only [d7013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d7013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7012 p = 1 := by simpa only [d7013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d7013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6392 (p : Pattern) (guard : d82170 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7013 p = 1 := by simpa only [d82170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d82170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6393 (p : Pattern) (guard : d1421 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1415 p = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6334 p hg
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1420 p = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6394 (p : Pattern) (guard : d1422 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1421 p = 1 := by simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6393 p hg
    simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6395 (p : Pattern) (guard : d1423 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1422 p = 1 := by simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6394 p hg
    simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d1423, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6396 (p : Pattern) (guard : d1424 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1423 p = 1 := by simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d1424, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6397 (p : Pattern) (guard : d6375 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1424 p = 1 := by simpa only [d6375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d6375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6398 (p : Pattern) (guard : d6376 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6375 p = 1 := by simpa only [d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6397 p hg
    simpa only [d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6399 (p : Pattern) (guard : d6377 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6376 p = 1 := by simpa only [d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6398 p hg
    simpa only [d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6400 (p : Pattern) (guard : d6378 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6377 p = 1 := by simpa only [d6378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d6378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6401 (p : Pattern) (guard : d6379 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6378 p = 1 := by simpa only [d6379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d6379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6402 (p : Pattern) (guard : d6380 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6379 p = 1 := by simpa only [d6380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d6380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6403 (p : Pattern) (guard : d82171 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82170 p = 1 := by simpa only [d82171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d82171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6380 p = 1 := by simpa only [d82171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d82171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6404 (p : Pattern) (guard : d82172 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82171 p = 1 := by simpa only [d82172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6403 p hg
    simpa only [d82172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6405 (p : Pattern) (guard : d82173 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82172 p = 1 := by simpa only [d82173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d82173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6406 (p : Pattern) (guard : d82174 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82174, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82174, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82173 p = 1 := by simpa only [d82174, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6405 p hg
    simpa only [d82174, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6407 (p : Pattern) (guard : d82175 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82174 p = 1 := by simpa only [d82175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d82175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6408 (p : Pattern) (guard : d1494 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1432 p = 1 := by simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6409 (p : Pattern) (guard : d1495 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1494 p = 1 := by simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6408 p hg
    simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6410 (p : Pattern) (guard : d1496 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1495 p = 1 := by simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6411 (p : Pattern) (guard : d1497 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1496 p = 1 := by simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6410 p hg
    simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6412 (p : Pattern) (guard : d1498 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1497 p = 1 := by simpa only [d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6411 p hg
    simpa only [d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6413 (p : Pattern) (guard : d1499 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1498 p = 1 := by simpa only [d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6414 (p : Pattern) (guard : d1500 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1499 p = 1 := by simpa only [d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6413 p hg
    simpa only [d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6415 (p : Pattern) (guard : d1501 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1500 p = 1 := by simpa only [d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6414 p hg
    simpa only [d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6416 (p : Pattern) (guard : d1502 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1501 p = 1 := by simpa only [d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6417 (p : Pattern) (guard : d1503 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1503, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1503, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1502 p = 1 := by simpa only [d1503, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d1503, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6418 (p : Pattern) (guard : d1504 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d1504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1503 p = 1 := by simpa only [d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6417 p hg
    simpa only [d1504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6419 (p : Pattern) (guard : d82176 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82175 p = 1 := by simpa only [d82176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d82176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1504 p = 1 := by simpa only [d82176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6418 p hg
    simpa only [d82176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6420 (p : Pattern) (guard : d82177 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82176 p = 1 := by simpa only [d82177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6419 p hg
    simpa only [d82177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6421 (p : Pattern) (guard : d82178 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82177 p = 1 := by simpa only [d82178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6420 p hg
    simpa only [d82178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6422 (p : Pattern) (guard : d82179 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82178 p = 1 := by simpa only [d82179, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6421 p hg
    simpa only [d82179, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82179, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d82179, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6423 (p : Pattern) (guard : d82180 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d82169 p = 1 := by simpa only [d82180, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6191 p hg
    simpa only [d82180, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82179 p = 1 := by simpa only [d82180, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d82180, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6424 (p : Pattern) (guard : d82181 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82180 p = 1 := by simpa only [d82181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6423 p hg
    simpa only [d82181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6425 (p : Pattern) (guard : d82182 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82181 p = 1 := by simpa only [d82182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d82182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6426 (p : Pattern) (guard : d82183 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82182 p = 1 := by simpa only [d82183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d82183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6427 (p : Pattern) (guard : d82184 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82183 p = 1 := by simpa only [d82184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d82184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6428 (p : Pattern) (guard : d82185 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82184 p = 1 := by simpa only [d82185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d82185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6429 (p : Pattern) (guard : d82186 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82185 p = 1 := by simpa only [d82186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6428 p hg
    simpa only [d82186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6430 (p : Pattern) (guard : d82187 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82186 p = 1 := by simpa only [d82187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6429 p hg
    simpa only [d82187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6431 (p : Pattern) (guard : d82188 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82187 p = 1 := by simpa only [d82188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d82188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6432 (p : Pattern) (guard : d82189 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d82147 p = 1 := by simpa only [d82189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5797 p hg
    simpa only [d82189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82188 p = 1 := by simpa only [d82189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d82189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6433 (p : Pattern) (guard : d308 p = 1) : d4 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare6434 (p : Pattern) (guard : d1519 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4406 p hg
    simpa only [d1519, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6435 (p : Pattern) (guard : d1520 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6436 (p : Pattern) (guard : d1521 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6437 (p : Pattern) (guard : d1522 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6436 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6438 (p : Pattern) (guard : d1523 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5798 p hg
    simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4813 p hg
    simpa only [d1523, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6439 (p : Pattern) (guard : d1524 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6438 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6440 (p : Pattern) (guard : d1525 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6439 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6441 (p : Pattern) (guard : d1526 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6440 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6442 (p : Pattern) (guard : d1527 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6441 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6443 (p : Pattern) (guard : d1528 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6444 (p : Pattern) (guard : d1529 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6442 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6443 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6445 (p : Pattern) (guard : d1530 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5916 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6444 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6446 (p : Pattern) (guard : d1531 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6447 (p : Pattern) (guard : d1532 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6446 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6448 (p : Pattern) (guard : d1533 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5460 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6447 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6449 (p : Pattern) (guard : d1534 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6448 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6450 (p : Pattern) (guard : d1535 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6449 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6451 (p : Pattern) (guard : d1536 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6450 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6452 (p : Pattern) (guard : d1537 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6453 (p : Pattern) (guard : d1538 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6452 p hg
    simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1538, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6454 (p : Pattern) (guard : d1539 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6436 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6447 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6455 (p : Pattern) (guard : d1540 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4407 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6456 (p : Pattern) (guard : d1541 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6455 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6457 (p : Pattern) (guard : d1542 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6440 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6456 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6458 (p : Pattern) (guard : d1543 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6454 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6457 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6459 (p : Pattern) (guard : d1544 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6460 (p : Pattern) (guard : d1545 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6458 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6459 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6461 (p : Pattern) (guard : d1546 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6444 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6462 (p : Pattern) (guard : d1547 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6446 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6463 (p : Pattern) (guard : d1548 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6447 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6462 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6464 (p : Pattern) (guard : d1549 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6463 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6465 (p : Pattern) (guard : d1550 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6464 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6466 (p : Pattern) (guard : d1551 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6450 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6465 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6467 (p : Pattern) (guard : d1552 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6461 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6466 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6468 (p : Pattern) (guard : d1553 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6467 p hg
    simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1553, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6469 (p : Pattern) (guard : d1554 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6468 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6470 (p : Pattern) (guard : d1555 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6469 p hg
    simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1555, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6471 (p : Pattern) (guard : d1556 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6470 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6472 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6471 p hg
    simpa only [d1557, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6473 (p : Pattern) (guard : d1558 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6472 p hg
    simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1558, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6474 (p : Pattern) (guard : d1559 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6456 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6475 (p : Pattern) (guard : d1560 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6463 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6476 (p : Pattern) (guard : d1561 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6475 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6477 (p : Pattern) (guard : d1562 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6476 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6478 (p : Pattern) (guard : d1563 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6462 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6479 (p : Pattern) (guard : d1564 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6480 (p : Pattern) (guard : d1565 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6479 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6481 (p : Pattern) (guard : d1566 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6465 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6482 (p : Pattern) (guard : d1567 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6477 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6481 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6483 (p : Pattern) (guard : d1568 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1568, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6484 (p : Pattern) (guard : d1569 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6468 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6483 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6485 (p : Pattern) (guard : d1570 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1570, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6486 (p : Pattern) (guard : d1571 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6485 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6487 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6486 p hg
    simpa only [d1572, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6488 (p : Pattern) (guard : d1573 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6487 p hg
    simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1573, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6489 (p : Pattern) (guard : d1574 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6473 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6488 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6490 (p : Pattern) (guard : d1575 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6491 (p : Pattern) (guard : d1576 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6490 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6492 (p : Pattern) (guard : d1577 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6491 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6493 (p : Pattern) (guard : d1578 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6494 (p : Pattern) (guard : d1579 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6492 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6493 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6495 (p : Pattern) (guard : d1580 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6494 p hg
    simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1580, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6496 (p : Pattern) (guard : d1581 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6483 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6495 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6497 (p : Pattern) (guard : d1582 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1582, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6498 (p : Pattern) (guard : d1583 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6497 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6499 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d1584, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
