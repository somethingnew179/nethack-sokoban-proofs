/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6300 (p : Pattern) (guard : d1412 p = 1) : d60 p ≤ (0 : Int) + d1437 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d60, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d60, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d60, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6299 p hg
    simpa only [d60, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6301 (p : Pattern) (guard : d1412 p = 1) : d61 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d61, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d61, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d61, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d61, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6302 (p : Pattern) (guard : d1412 p = 1) : d62 p ≤ (0 : Int) + d1430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d62, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6280 p hg
    simpa only [d62, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d62, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6301 p hg
    simpa only [d62, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6303 (p : Pattern) (guard : d1412 p = 1) : d63 p ≤ (0 : Int) + d1433 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d63, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6302 p hg
    simpa only [d63, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d63, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6295 p hg
    simpa only [d63, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6304 (p : Pattern) (guard : d1412 p = 1) : d64 p ≤ (0 : Int) + d1438 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d64, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6300 p hg
    simpa only [d64, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d64, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6303 p hg
    simpa only [d64, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6305 (p : Pattern) (guard : d1412 p = 1) : d65 p ≤ (0 : Int) + d1439 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d65, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6297 p hg
    simpa only [d65, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d65, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6304 p hg
    simpa only [d65, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6306 (p : Pattern) (guard : d1412 p = 1) : d66 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d66, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6290 p hg
    simpa only [d66, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d66, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6305 p hg
    simpa only [d66, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6307 (p : Pattern) (guard : d1412 p = 1) : d67 p ≤ (0 : Int) + d1441 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d67, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d67, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d67, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6306 p hg
    simpa only [d67, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6308 (p : Pattern) (guard : d1412 p = 1) : d68 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d68, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6279 p hg
    simpa only [d68, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d68, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d68, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6309 (p : Pattern) (guard : d1412 p = 1) : d69 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d69, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6279 p hg
    simpa only [d69, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d69, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d69, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6310 (p : Pattern) (guard : d1412 p = 1) : d70 p ≤ (0 : Int) + d1444 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d70, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d70, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d70, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d70, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6311 (p : Pattern) (guard : d1412 p = 1) : d71 p ≤ (0 : Int) + d1445 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d71, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6261 p hg
    simpa only [d71, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d71, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6310 p hg
    simpa only [d71, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6312 (p : Pattern) (guard : d1412 p = 1) : d72 p ≤ (0 : Int) + d1446 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d72, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6309 p hg
    simpa only [d72, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d72, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6311 p hg
    simpa only [d72, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6313 (p : Pattern) (guard : d1412 p = 1) : d73 p ≤ (0 : Int) + d1447 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d73, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6264 p hg
    simpa only [d73, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d73, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6312 p hg
    simpa only [d73, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6314 (p : Pattern) (guard : d1412 p = 1) : d74 p ≤ (0 : Int) + d1448 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d74, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6265 p hg
    simpa only [d74, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d74, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6313 p hg
    simpa only [d74, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6315 (p : Pattern) (guard : d1412 p = 1) : d75 p ≤ (0 : Int) + d1449 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d75, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6308 p hg
    simpa only [d75, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d75, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6310 p hg
    simpa only [d75, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6316 (p : Pattern) (guard : d1412 p = 1) : d76 p ≤ (0 : Int) + d1450 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d76, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6264 p hg
    simpa only [d76, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d76, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d76, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6317 (p : Pattern) (guard : d1412 p = 1) : d77 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d77, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6265 p hg
    simpa only [d77, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d77, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6316 p hg
    simpa only [d77, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6318 (p : Pattern) (guard : d1412 p = 1) : d78 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d78, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6314 p hg
    simpa only [d78, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d78, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6317 p hg
    simpa only [d78, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6319 (p : Pattern) (guard : d1412 p = 1) : d79 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d79, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6285 p hg
    simpa only [d79, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d79, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d79, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6320 (p : Pattern) (guard : d1412 p = 1) : d80 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d80, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6286 p hg
    simpa only [d80, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d80, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6319 p hg
    simpa only [d80, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6321 (p : Pattern) (guard : d1412 p = 1) : d81 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d81, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6296 p hg
    simpa only [d81, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d81, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d81, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6322 (p : Pattern) (guard : d1412 p = 1) : d82 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d82, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6297 p hg
    simpa only [d82, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d82, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6321 p hg
    simpa only [d82, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6323 (p : Pattern) (guard : d1412 p = 1) : d83 p ≤ (0 : Int) + d1457 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d83, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6320 p hg
    simpa only [d83, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d83, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6322 p hg
    simpa only [d83, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6324 (p : Pattern) (guard : d1412 p = 1) : d84 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d84, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6318 p hg
    simpa only [d84, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d84, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6323 p hg
    simpa only [d84, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6325 (p : Pattern) (guard : d1412 p = 1) : d85 p ≤ (0 : Int) + d1459 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d85, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6307 p hg
    simpa only [d85, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d85, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6324 p hg
    simpa only [d85, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6326 (p : Pattern) (guard : d1412 p = 1) : d86 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d86, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6244 p hg
    simpa only [d86, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d86, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6292 p hg
    simpa only [d86, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6327 (p : Pattern) (guard : d1412 p = 1) : d87 p ≤ (0 : Int) + d1461 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d87, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d87, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d87, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6294 p hg
    simpa only [d87, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6328 (p : Pattern) (guard : d1412 p = 1) : d88 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d88, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6326 p hg
    simpa only [d88, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d88, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6327 p hg
    simpa only [d88, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6329 (p : Pattern) (guard : d1412 p = 1) : d89 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d89, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6326 p hg
    simpa only [d89, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d89, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6328 p hg
    simpa only [d89, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6330 (p : Pattern) (guard : d1412 p = 1) : d90 p ≤ (0 : Int) + d1464 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d90, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d90, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d90, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6298 p hg
    simpa only [d90, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6331 (p : Pattern) (guard : d1412 p = 1) : d91 p ≤ (0 : Int) + d1465 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d91, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6326 p hg
    simpa only [d91, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d91, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6330 p hg
    simpa only [d91, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6332 (p : Pattern) (guard : d1412 p = 1) : d92 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d92, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6276 p hg
    simpa only [d92, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d92, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6301 p hg
    simpa only [d92, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6333 (p : Pattern) (guard : d1412 p = 1) : d93 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d93, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6332 p hg
    simpa only [d93, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d93, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6327 p hg
    simpa only [d93, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6334 (p : Pattern) (guard : d1412 p = 1) : d94 p ≤ (0 : Int) + d1466 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d94, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6331 p hg
    simpa only [d94, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d94, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d94, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6335 (p : Pattern) (guard : d1412 p = 1) : d95 p ≤ (0 : Int) + d1467 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d95, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6329 p hg
    simpa only [d95, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d95, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6334 p hg
    simpa only [d95, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6336 (p : Pattern) (guard : d1412 p = 1) : d96 p ≤ (0 : Int) + d1468 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d96, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d96, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d96, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6335 p hg
    simpa only [d96, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6337 (p : Pattern) (guard : d1412 p = 1) : d97 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d97, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6249 p hg
    simpa only [d97, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d97, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d97, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6338 (p : Pattern) (guard : d1412 p = 1) : d98 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d98, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6249 p hg
    simpa only [d98, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d98, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6337 p hg
    simpa only [d98, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6339 (p : Pattern) (guard : d1412 p = 1) : d99 p ≤ (0 : Int) + d1446 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d99, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6338 p hg
    simpa only [d99, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d99, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6311 p hg
    simpa only [d99, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6340 (p : Pattern) (guard : d1412 p = 1) : d100 p ≤ (0 : Int) + d1469 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d100, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6338 p hg
    simpa only [d100, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d100, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d100, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6341 (p : Pattern) (guard : d1412 p = 1) : d101 p ≤ (0 : Int) + d1446 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6312 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6342 (p : Pattern) (guard : d1412 p = 1) : d102 p ≤ (0 : Int) + d1470 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d102, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6340 p hg
    simpa only [d102, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d102, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6341 p hg
    simpa only [d102, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6343 (p : Pattern) (guard : d1412 p = 1) : d103 p ≤ (0 : Int) + d1471 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d103, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6336 p hg
    simpa only [d103, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d103, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6342 p hg
    simpa only [d103, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6344 (p : Pattern) (guard : d1412 p = 1) : d104 p ≤ (0 : Int) + d1472 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d104, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6328 p hg
    simpa only [d104, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d104, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d104, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6345 (p : Pattern) (guard : d1412 p = 1) : d105 p ≤ (0 : Int) + d1473 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d105, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6329 p hg
    simpa only [d105, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d105, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6344 p hg
    simpa only [d105, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6346 (p : Pattern) (guard : d1412 p = 1) : d106 p ≤ (0 : Int) + d1474 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d106, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6317 p hg
    simpa only [d106, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d106, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6345 p hg
    simpa only [d106, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6347 (p : Pattern) (guard : d1412 p = 1) : d107 p ≤ (0 : Int) + d1475 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d107, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6339 p hg
    simpa only [d107, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d107, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d107, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6348 (p : Pattern) (guard : d1412 p = 1) : d108 p ≤ (0 : Int) + d1476 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d108, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6340 p hg
    simpa only [d108, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d108, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6347 p hg
    simpa only [d108, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6349 (p : Pattern) (guard : d1412 p = 1) : d109 p ≤ (0 : Int) + d1449 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d109, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6337 p hg
    simpa only [d109, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d109, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6310 p hg
    simpa only [d109, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6350 (p : Pattern) (guard : d1412 p = 1) : d110 p ≤ (0 : Int) + d1477 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d110, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6337 p hg
    simpa only [d110, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d110, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d110, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6351 (p : Pattern) (guard : d1412 p = 1) : d111 p ≤ (0 : Int) + d1478 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d111, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d111, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d111, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d111, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6352 (p : Pattern) (guard : d1412 p = 1) : d112 p ≤ (0 : Int) + d1479 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d112, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6350 p hg
    simpa only [d112, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d112, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6351 p hg
    simpa only [d112, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6353 (p : Pattern) (guard : d1412 p = 1) : d113 p ≤ (0 : Int) + d1480 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d113, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6348 p hg
    simpa only [d113, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d113, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6352 p hg
    simpa only [d113, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6354 (p : Pattern) (guard : d1412 p = 1) : d114 p ≤ (0 : Int) + d1481 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d114, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6346 p hg
    simpa only [d114, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d114, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6353 p hg
    simpa only [d114, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6355 (p : Pattern) (guard : d1412 p = 1) : d115 p ≤ (0 : Int) + d1482 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d115, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6343 p hg
    simpa only [d115, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d115, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6354 p hg
    simpa only [d115, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6356 (p : Pattern) (guard : d1412 p = 1) : d116 p ≤ (0 : Int) + d1483 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d116, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6325 p hg
    simpa only [d116, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d116, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6355 p hg
    simpa only [d116, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6357 (p : Pattern) (guard : d1412 p = 1) : d117 p ≤ (0 : Int) + d1484 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d117, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6317 p hg
    simpa only [d117, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d117, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6323 p hg
    simpa only [d117, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6358 (p : Pattern) (guard : d1412 p = 1) : d118 p ≤ (0 : Int) + d1485 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d118, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6307 p hg
    simpa only [d118, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d118, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6357 p hg
    simpa only [d118, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6359 (p : Pattern) (guard : d1412 p = 1) : d119 p ≤ (0 : Int) + d1486 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d119, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d119, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d119, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6256 p hg
    simpa only [d119, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6360 (p : Pattern) (guard : d1412 p = 1) : d120 p ≤ (0 : Int) + d1487 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d120, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6359 p hg
    simpa only [d120, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d120, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6298 p hg
    simpa only [d120, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6361 (p : Pattern) (guard : d1412 p = 1) : d121 p ≤ (0 : Int) + d1488 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d121, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6326 p hg
    simpa only [d121, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d121, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6360 p hg
    simpa only [d121, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6362 (p : Pattern) (guard : d1412 p = 1) : d122 p ≤ (0 : Int) + d1489 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d122, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6361 p hg
    simpa only [d122, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d122, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6333 p hg
    simpa only [d122, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6363 (p : Pattern) (guard : d1412 p = 1) : d123 p ≤ (0 : Int) + d1490 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d123, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6329 p hg
    simpa only [d123, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d123, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6362 p hg
    simpa only [d123, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6364 (p : Pattern) (guard : d1412 p = 1) : d124 p ≤ (0 : Int) + d1491 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d124, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d124, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d124, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6363 p hg
    simpa only [d124, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6365 (p : Pattern) (guard : d1412 p = 1) : d125 p ≤ (0 : Int) + d1449 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6349 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6315 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6366 (p : Pattern) (guard : d1412 p = 1) : d126 p ≤ (0 : Int) + d1492 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d126, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6350 p hg
    simpa only [d126, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d126, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6365 p hg
    simpa only [d126, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6367 (p : Pattern) (guard : d1412 p = 1) : d127 p ≤ (0 : Int) + d1493 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d127, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6342 p hg
    simpa only [d127, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d127, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6366 p hg
    simpa only [d127, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6368 (p : Pattern) (guard : d1412 p = 1) : d128 p ≤ (0 : Int) + d1494 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d128, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6364 p hg
    simpa only [d128, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d128, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6367 p hg
    simpa only [d128, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6369 (p : Pattern) (guard : d1412 p = 1) : d129 p ≤ (0 : Int) + d1495 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d129, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6317 p hg
    simpa only [d129, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d129, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6322 p hg
    simpa only [d129, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6370 (p : Pattern) (guard : d1412 p = 1) : d130 p ≤ (0 : Int) + d1496 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d130, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6352 p hg
    simpa only [d130, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d130, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d130, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6371 (p : Pattern) (guard : d1412 p = 1) : d131 p ≤ (0 : Int) + d1497 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d131, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6369 p hg
    simpa only [d131, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d131, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6370 p hg
    simpa only [d131, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6372 (p : Pattern) (guard : d1412 p = 1) : d132 p ≤ (0 : Int) + d1498 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d132, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6368 p hg
    simpa only [d132, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d132, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6371 p hg
    simpa only [d132, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6373 (p : Pattern) (guard : d1412 p = 1) : d133 p ≤ (0 : Int) + d1499 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d133, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6358 p hg
    simpa only [d133, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d133, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6372 p hg
    simpa only [d133, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6374 (p : Pattern) (guard : d1412 p = 1) : d134 p ≤ (0 : Int) + d1500 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d134, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6356 p hg
    simpa only [d134, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d134, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6373 p hg
    simpa only [d134, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6375 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6376 (p : Pattern) (guard : d873 p = 1) : d538 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d873, d538, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6377 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6378 (p : Pattern) (guard : d873 p = 1) : d539 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d873, d539, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6379 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6380 (p : Pattern) (guard : d873 p = 1) : d540 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d873, d540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6381 (p : Pattern) (guard : d873 p = 1) : d541 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6380 p hg
    simpa only [d541, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6382 (p : Pattern) (guard : d873 p = 1) : d542 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d542, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6383 (p : Pattern) (guard : d873 p = 1) : d543 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d543, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6384 (p : Pattern) (guard : d873 p = 1) : d544 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6382 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6385 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6386 (p : Pattern) (guard : d873 p = 1) : d545 p ≤ (0 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2359 p hg
    simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6385 p hg
    simpa only [d873, d545, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6387 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6388 (p : Pattern) (guard : d873 p = 1) : d546 p ≤ (0 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2362 p hg
    simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6387 p hg
    simpa only [d873, d546, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6389 (p : Pattern) (guard : d873 p = 1) : d547 p ≤ (0 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d547, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6390 (p : Pattern) (guard : d873 p = 1) : d548 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d548, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6391 (p : Pattern) (guard : d873 p = 1) : d549 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6383 p hg
    simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6390 p hg
    simpa only [d549, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6392 (p : Pattern) (guard : d873 p = 1) : d550 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d550, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6384 p hg
    simpa only [d550, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d550, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6391 p hg
    simpa only [d550, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6393 (p : Pattern) (guard : d0 p = 1) : d555 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6394 (p : Pattern) (guard : d1148 p = 1) : d556 p ≤ (0 : Int) + d256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d556, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d1148, d556, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d556, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6393 p hg
    simpa only [d1148, d556, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6395 (p : Pattern) (guard : d873 p = 1) : d557 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d557, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6396 (p : Pattern) (guard : d873 p = 1) : d558 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d558, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d558, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d558, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6395 p hg
    simpa only [d558, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6397 (p : Pattern) (guard : d0 p = 1) : d560 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6398 (p : Pattern) (guard : d1148 p = 1) : d561 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d561, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d1148, d561, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d561, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6397 p hg
    simpa only [d1148, d561, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6399 (p : Pattern) (guard : d873 p = 1) : d562 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d562, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6400 (p : Pattern) (guard : d873 p = 1) : d563 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6381 p hg
    simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d563, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6401 (p : Pattern) (guard : d873 p = 1) : d564 p ≤ (0 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d564, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6402 (p : Pattern) (guard : d873 p = 1) : d565 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6389 p hg
    simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d565, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6403 (p : Pattern) (guard : d873 p = 1) : d566 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6402 p hg
    simpa only [d566, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6404 (p : Pattern) (guard : d873 p = 1) : d567 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d567, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6400 p hg
    simpa only [d567, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d567, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6403 p hg
    simpa only [d567, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6405 (p : Pattern) (guard : d0 p = 1) : d571 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6406 (p : Pattern) (guard : d1148 p = 1) : d572 p ≤ (0 : Int) + d258 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d572, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d1148, d572, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d572, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6405 p hg
    simpa only [d1148, d572, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6407 (p : Pattern) (guard : d1148 p = 1) : d573 p ≤ (0 : Int) + d259 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d573, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6398 p hg
    simpa only [d573, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d573, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6406 p hg
    simpa only [d573, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6408 (p : Pattern) (guard : d1148 p = 1) : d574 p ≤ (0 : Int) + d260 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d574, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6394 p hg
    simpa only [d574, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d574, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d574, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6409 (p : Pattern) (guard : d0 p = 1) : d581 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6410 (p : Pattern) (guard : d1148 p = 1) : d582 p ≤ (0 : Int) + d256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d582, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d1148, d582, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d582, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6409 p hg
    simpa only [d1148, d582, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6411 (p : Pattern) (guard : d0 p = 1) : d587 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6412 (p : Pattern) (guard : d1148 p = 1) : d588 p ≤ (0 : Int) + d261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d588, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6392 p hg
    simpa only [d1148, d588, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d588, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6411 p hg
    simpa only [d1148, d588, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6413 (p : Pattern) (guard : d1148 p = 1) : d589 p ≤ (0 : Int) + d262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d589, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6410 p hg
    simpa only [d589, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d589, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d589, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6414 (p : Pattern) (guard : d0 p = 1) : d590 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6415 (p : Pattern) (guard : d1148 p = 1) : d591 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d591, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6396 p hg
    simpa only [d1148, d591, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d591, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6414 p hg
    simpa only [d1148, d591, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6416 (p : Pattern) (guard : d0 p = 1) : d592 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6417 (p : Pattern) (guard : d1148 p = 1) : d593 p ≤ (0 : Int) + d263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d593, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6404 p hg
    simpa only [d1148, d593, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d593, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d1148, d593, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6418 (p : Pattern) (guard : d1148 p = 1) : d594 p ≤ (0 : Int) + d264 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d594, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6415 p hg
    simpa only [d594, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d594, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6417 p hg
    simpa only [d594, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6419 (p : Pattern) (guard : d1148 p = 1) : d595 p ≤ (0 : Int) + d265 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d595, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6413 p hg
    simpa only [d595, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d595, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6418 p hg
    simpa only [d595, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6420 (p : Pattern) (guard : d1148 p = 1) : d596 p ≤ (0 : Int) + d266 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d596, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6408 p hg
    simpa only [d596, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d596, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6419 p hg
    simpa only [d596, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6421 (p : Pattern) (guard : d873 p = 1) : d597 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d597, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6376 p hg
    simpa only [d597, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d597, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d597, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6422 (p : Pattern) (guard : d873 p = 1) : d598 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6378 p hg
    simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d598, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6423 (p : Pattern) (guard : d873 p = 1) : d599 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6421 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6424 (p : Pattern) (guard : d873 p = 1) : d600 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6386 p hg
    simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6401 p hg
    simpa only [d600, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6425 (p : Pattern) (guard : d873 p = 1) : d601 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d601, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6426 (p : Pattern) (guard : d873 p = 1) : d602 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d602, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6423 p hg
    simpa only [d602, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d602, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6425 p hg
    simpa only [d602, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6427 (p : Pattern) (guard : d0 p = 1) : d606 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6428 (p : Pattern) (guard : d1148 p = 1) : d607 p ≤ (0 : Int) + d267 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d607, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6426 p hg
    simpa only [d1148, d607, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d607, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6427 p hg
    simpa only [d1148, d607, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6429 (p : Pattern) (guard : d1148 p = 1) : d608 p ≤ (0 : Int) + d268 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d608, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6394 p hg
    simpa only [d608, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1148 p = 1 := by simpa only [d608, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6428 p hg
    simpa only [d608, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6430 (p : Pattern) (guard : d873 p = 1) : d576 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6380 p hg
    simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d576, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6431 (p : Pattern) (guard : d873 p = 1) : d577 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6380 p hg
    simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d577, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6432 (p : Pattern) (guard : d873 p = 1) : d578 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d578, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6433 (p : Pattern) (guard : d873 p = 1) : d579 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6388 p hg
    simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d579, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6434 (p : Pattern) (guard : d873 p = 1) : d580 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d580, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6435 (p : Pattern) (guard : d873 p = 1) : d609 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6431 p hg
    simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6434 p hg
    simpa only [d609, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6436 (p : Pattern) (guard : d0 p = 1) : d580 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6437 (p : Pattern) (guard : d1148 p = 1) : d610 p ≤ (0 : Int) + d269 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d610, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d1148, d610, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d610, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6436 p hg
    simpa only [d1148, d610, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6438 (p : Pattern) (guard : d0 p = 1) : d580 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6439 (p : Pattern) (guard : d1148 p = 1) : d610 p ≤ (0 : Int) + d270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1148, d610, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d1148, d610, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, d610, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6438 p hg
    simpa only [d1148, d610, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
