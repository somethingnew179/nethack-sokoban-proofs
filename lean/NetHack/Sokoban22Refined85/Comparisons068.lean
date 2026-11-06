/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9520 (p : Pattern) (guard : d4303 p = 1) : d1356 p ≤ (0 : Int) + d678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1356, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9424 p hg
    simpa only [d1356, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1356, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9519 p hg
    simpa only [d1356, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9521 (p : Pattern) (guard : d4303 p = 1) : d1357 p ≤ (0 : Int) + d679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1357, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9399 p hg
    simpa only [d1357, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1357, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9520 p hg
    simpa only [d1357, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9522 (p : Pattern) (guard : d0 p = 1) : d1360 p ≤ (0 : Int) + d453 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9523 (p : Pattern) (guard : d4303 p = 1) : d1361 p ≤ (0 : Int) + d695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1361, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9455 p hg
    simpa only [d4303, d1361, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1361, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9522 p hg
    simpa only [d4303, d1361, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9524 (p : Pattern) (guard : d0 p = 1) : d1334 p ≤ (0 : Int) + d456 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9525 (p : Pattern) (guard : d4303 p = 1) : d1362 p ≤ (0 : Int) + d696 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1362, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9467 p hg
    simpa only [d4303, d1362, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1362, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9524 p hg
    simpa only [d4303, d1362, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9526 (p : Pattern) (guard : d4303 p = 1) : d1363 p ≤ (0 : Int) + d697 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1363, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9523 p hg
    simpa only [d1363, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1363, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9525 p hg
    simpa only [d1363, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9527 (p : Pattern) (guard : d0 p = 1) : d1334 p ≤ (0 : Int) + d461 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9528 (p : Pattern) (guard : d4303 p = 1) : d1364 p ≤ (0 : Int) + d698 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1364, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9475 p hg
    simpa only [d4303, d1364, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1364, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9527 p hg
    simpa only [d4303, d1364, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9529 (p : Pattern) (guard : d4303 p = 1) : d1365 p ≤ (0 : Int) + d699 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1365, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9528 p hg
    simpa only [d1365, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1365, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d1365, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9530 (p : Pattern) (guard : d4303 p = 1) : d1366 p ≤ (0 : Int) + d700 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1366, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9526 p hg
    simpa only [d1366, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1366, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9529 p hg
    simpa only [d1366, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9531 (p : Pattern) (guard : d4148 p = 1) : d1367 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1367, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9481 p hg
    simpa only [d1367, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1367, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1367, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9532 (p : Pattern) (guard : d4148 p = 1) : d1368 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1368, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9531 p hg
    simpa only [d1368, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1368, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1368, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9533 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d270 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9534 (p : Pattern) (guard : d4148 p = 1) : d1369 p ≤ (0 : Int) + d271 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1369, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d1369, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1369, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9533 p hg
    simpa only [d4148, d1369, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9535 (p : Pattern) (guard : d4148 p = 1) : d1370 p ≤ (0 : Int) + d275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1370, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3850 p hg
    simpa only [d4148, d1370, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1370, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d4148, d1370, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9536 (p : Pattern) (guard : d4148 p = 1) : d1371 p ≤ (0 : Int) + d276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1371, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9534 p hg
    simpa only [d1371, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1371, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d1371, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9537 (p : Pattern) (guard : d4148 p = 1) : d1372 p ≤ (0 : Int) + d279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1372, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d1372, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1372, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d1372, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9538 (p : Pattern) (guard : d4148 p = 1) : d1373 p ≤ (0 : Int) + d280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1373, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9536 p hg
    simpa only [d1373, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1373, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9537 p hg
    simpa only [d1373, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9539 (p : Pattern) (guard : d4148 p = 1) : d1374 p ≤ (0 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1374, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9532 p hg
    simpa only [d1374, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1374, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9538 p hg
    simpa only [d1374, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9540 (p : Pattern) (guard : d0 p = 1) : d1379 p ≤ (0 : Int) + d471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9541 (p : Pattern) (guard : d4303 p = 1) : d1380 p ≤ (0 : Int) + d701 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1380, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9539 p hg
    simpa only [d4303, d1380, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1380, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9540 p hg
    simpa only [d4303, d1380, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9542 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9543 (p : Pattern) (guard : d4148 p = 1) : d1296 p ≤ (0 : Int) + d291 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1296, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1296, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1296, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9542 p hg
    simpa only [d4148, d1296, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9544 (p : Pattern) (guard : d4148 p = 1) : d1369 p ≤ (0 : Int) + d293 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1369, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d1369, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1369, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2444 p hg
    simpa only [d4148, d1369, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9545 (p : Pattern) (guard : d4148 p = 1) : d1381 p ≤ (0 : Int) + d294 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1381, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9543 p hg
    simpa only [d1381, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1381, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1381, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9546 (p : Pattern) (guard : d4148 p = 1) : d1382 p ≤ (0 : Int) + d295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1382, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1382, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1382, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d1382, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9547 (p : Pattern) (guard : d4148 p = 1) : d1383 p ≤ (0 : Int) + d296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1383, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9545 p hg
    simpa only [d1383, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1383, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9546 p hg
    simpa only [d1383, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9548 (p : Pattern) (guard : d4148 p = 1) : d1384 p ≤ (0 : Int) + d297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1384, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9547 p hg
    simpa only [d1384, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1384, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1384, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9549 (p : Pattern) (guard : d0 p = 1) : d1390 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9550 (p : Pattern) (guard : d4303 p = 1) : d1391 p ≤ (0 : Int) + d702 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d1391, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9548 p hg
    simpa only [d4303, d1391, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d1391, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9549 p hg
    simpa only [d4303, d1391, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9551 (p : Pattern) (guard : d4303 p = 1) : d1392 p ≤ (0 : Int) + d703 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1392, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9541 p hg
    simpa only [d1392, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1392, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9550 p hg
    simpa only [d1392, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9552 (p : Pattern) (guard : d4303 p = 1) : d1393 p ≤ (0 : Int) + d704 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1393, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9550 p hg
    simpa only [d1393, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1393, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1393, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9553 (p : Pattern) (guard : d4303 p = 1) : d1394 p ≤ (0 : Int) + d705 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1394, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9551 p hg
    simpa only [d1394, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1394, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9552 p hg
    simpa only [d1394, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9554 (p : Pattern) (guard : d4303 p = 1) : d1395 p ≤ (0 : Int) + d706 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1395, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9530 p hg
    simpa only [d1395, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1395, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9553 p hg
    simpa only [d1395, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9555 (p : Pattern) (guard : d4303 p = 1) : d1396 p ≤ (0 : Int) + d707 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1396, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9399 p hg
    simpa only [d1396, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1396, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9554 p hg
    simpa only [d1396, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9556 (p : Pattern) (guard : d4303 p = 1) : d1397 p ≤ (0 : Int) + d708 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1397, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9521 p hg
    simpa only [d1397, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1397, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9555 p hg
    simpa only [d1397, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9557 (p : Pattern) (guard : d4303 p = 1) : d1398 p ≤ (0 : Int) + d709 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1398, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9512 p hg
    simpa only [d1398, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1398, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9556 p hg
    simpa only [d1398, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9558 (p : Pattern) (guard : d0 p = 1) : d1163 p ≤ (2 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9559 (p : Pattern) (guard : d0 p = 1) : d352 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9560 (p : Pattern) (guard : d4148 p = 1) : d1164 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9559 p hg
    simpa only [d4148, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9561 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9562 (p : Pattern) (guard : d4148 p = 1) : d1165 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1165, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d4148, d1165, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1165, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9561 p hg
    simpa only [d4148, d1165, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9563 (p : Pattern) (guard : d4148 p = 1) : d1166 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1166, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9560 p hg
    simpa only [d1166, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1166, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9562 p hg
    simpa only [d1166, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9564 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9565 (p : Pattern) (guard : d4148 p = 1) : d1167 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1167, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d4148, d1167, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1167, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9564 p hg
    simpa only [d4148, d1167, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9566 (p : Pattern) (guard : d4148 p = 1) : d63 p ≤ (2 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d4148, d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4148, d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9567 (p : Pattern) (guard : d4148 p = 1) : d1168 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1168, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9565 p hg
    simpa only [d1168, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1168, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9566 p hg
    simpa only [d1168, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9568 (p : Pattern) (guard : d4148 p = 1) : d1169 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1169, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9563 p hg
    simpa only [d1169, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1169, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9567 p hg
    simpa only [d1169, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9569 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (2 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9570 (p : Pattern) (guard : d4148 p = 1) : d1170 p ≤ (2 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1170, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6681 p hg
    simpa only [d4148, d1170, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1170, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9569 p hg
    simpa only [d4148, d1170, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9571 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (2 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d66, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d66, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9572 (p : Pattern) (guard : d4148 p = 1) : d1171 p ≤ (2 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1171, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9571 p hg
    simpa only [d4148, d1171, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1171, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d4148, d1171, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9573 (p : Pattern) (guard : d4148 p = 1) : d1172 p ≤ (2 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1172, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9570 p hg
    simpa only [d1172, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1172, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9572 p hg
    simpa only [d1172, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9574 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (2 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d66, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d66, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9575 (p : Pattern) (guard : d4148 p = 1) : d1171 p ≤ (2 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1171, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9574 p hg
    simpa only [d4148, d1171, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1171, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d4148, d1171, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9576 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (2 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d72, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d72, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9577 (p : Pattern) (guard : d4148 p = 1) : d73 p ≤ (2 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d73, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9576 p hg
    simpa only [d4148, d73, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d73, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4148, d73, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9578 (p : Pattern) (guard : d4148 p = 1) : d1173 p ≤ (2 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1173, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9575 p hg
    simpa only [d1173, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1173, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9577 p hg
    simpa only [d1173, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9579 (p : Pattern) (guard : d4148 p = 1) : d1174 p ≤ (2 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1174, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1174, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1174, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9578 p hg
    simpa only [d1174, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9580 (p : Pattern) (guard : d4148 p = 1) : d1175 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1175, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9568 p hg
    simpa only [d1175, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1175, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9579 p hg
    simpa only [d1175, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9581 (p : Pattern) (guard : d4149 p = 1) : d1176 p ≤ (2 : Int) + d52 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9558 p hg
    simpa only [d4149, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9580 p hg
    simpa only [d4149, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9582 (p : Pattern) (guard : d0 p = 1) : d1184 p ≤ (2 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9583 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9584 (p : Pattern) (guard : d4148 p = 1) : d1185 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9583 p hg
    simpa only [d4148, d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9585 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d4148, d1181, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d4148, d1181, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9586 (p : Pattern) (guard : d4148 p = 1) : d1186 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1186, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9584 p hg
    simpa only [d1186, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1186, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d1186, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9587 (p : Pattern) (guard : d4148 p = 1) : d1182 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1182, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d1182, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1182, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9566 p hg
    simpa only [d1182, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9588 (p : Pattern) (guard : d4148 p = 1) : d1187 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1187, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9586 p hg
    simpa only [d1187, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1187, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1187, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9589 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d78 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9590 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (2 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9589 p hg
    simpa only [d4148, d1181, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9591 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9592 (p : Pattern) (guard : d4148 p = 1) : d1188 p ≤ (2 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1188, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9590 p hg
    simpa only [d1188, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1188, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9591 p hg
    simpa only [d1188, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9593 (p : Pattern) (guard : d4148 p = 1) : d1189 p ≤ (2 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1189, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9592 p hg
    simpa only [d1189, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1189, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d1189, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9594 (p : Pattern) (guard : d4148 p = 1) : d1190 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1190, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9588 p hg
    simpa only [d1190, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1190, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9593 p hg
    simpa only [d1190, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9595 (p : Pattern) (guard : d4149 p = 1) : d1191 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9582 p hg
    simpa only [d4149, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9594 p hg
    simpa only [d4149, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9596 (p : Pattern) (guard : d4149 p = 1) : d1192 p ≤ (2 : Int) + d4797 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1192, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9581 p hg
    simpa only [d1192, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1192, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9595 p hg
    simpa only [d1192, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9597 (p : Pattern) (guard : d0 p = 1) : d1196 p ≤ (2 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9598 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9599 (p : Pattern) (guard : d4148 p = 1) : d1197 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9598 p hg
    simpa only [d4148, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9600 (p : Pattern) (guard : d4148 p = 1) : d1198 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1198, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9599 p hg
    simpa only [d1198, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1198, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d1198, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9601 (p : Pattern) (guard : d4148 p = 1) : d1199 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1199, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9600 p hg
    simpa only [d1199, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1199, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1199, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9602 (p : Pattern) (guard : d4148 p = 1) : d1200 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1200, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1200, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1200, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9593 p hg
    simpa only [d1200, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9603 (p : Pattern) (guard : d4149 p = 1) : d1201 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d4149, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9602 p hg
    simpa only [d4149, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9604 (p : Pattern) (guard : d0 p = 1) : d1204 p ≤ (2 : Int) + d94 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9605 (p : Pattern) (guard : d4148 p = 1) : d63 p ≤ (2 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d4148, d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6730 p hg
    simpa only [d4148, d63, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9606 (p : Pattern) (guard : d4148 p = 1) : d91 p ≤ (2 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9605 p hg
    simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9591 p hg
    simpa only [d91, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9607 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9591 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9608 (p : Pattern) (guard : d4148 p = 1) : d93 p ≤ (2 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9606 p hg
    simpa only [d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9607 p hg
    simpa only [d93, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9609 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9607 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9610 (p : Pattern) (guard : d4148 p = 1) : d95 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9608 p hg
    simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9609 p hg
    simpa only [d95, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9611 (p : Pattern) (guard : d4149 p = 1) : d1205 p ≤ (2 : Int) + d94 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9604 p hg
    simpa only [d4149, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9610 p hg
    simpa only [d4149, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9612 (p : Pattern) (guard : d4149 p = 1) : d1206 p ≤ (2 : Int) + d4798 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1206, d4798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9603 p hg
    simpa only [d1206, d4798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1206, d4798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9611 p hg
    simpa only [d1206, d4798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9613 (p : Pattern) (guard : d4149 p = 1) : d1207 p ≤ (2 : Int) + d4799 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1207, d4799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1207, d4799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1207, d4799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9612 p hg
    simpa only [d1207, d4799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9614 (p : Pattern) (guard : d0 p = 1) : d1215 p ≤ (2 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9615 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9616 (p : Pattern) (guard : d4148 p = 1) : d1154 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9615 p hg
    simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9617 (p : Pattern) (guard : d4148 p = 1) : d1216 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1216, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9616 p hg
    simpa only [d1216, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1216, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d1216, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9618 (p : Pattern) (guard : d4148 p = 1) : d1217 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1217, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9617 p hg
    simpa only [d1217, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1217, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1217, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9619 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9620 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (2 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6681 p hg
    simpa only [d4148, d1181, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9619 p hg
    simpa only [d4148, d1181, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9621 (p : Pattern) (guard : d4148 p = 1) : d1218 p ≤ (2 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1218, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9620 p hg
    simpa only [d1218, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1218, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9572 p hg
    simpa only [d1218, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9622 (p : Pattern) (guard : d4148 p = 1) : d1219 p ≤ (2 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1219, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9621 p hg
    simpa only [d1219, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1219, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9578 p hg
    simpa only [d1219, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9623 (p : Pattern) (guard : d4148 p = 1) : d1220 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1220, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9618 p hg
    simpa only [d1220, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1220, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9622 p hg
    simpa only [d1220, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9624 (p : Pattern) (guard : d4149 p = 1) : d1221 p ≤ (2 : Int) + d52 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9614 p hg
    simpa only [d4149, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9623 p hg
    simpa only [d4149, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9625 (p : Pattern) (guard : d0 p = 1) : d1224 p ≤ (2 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9626 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9627 (p : Pattern) (guard : d4148 p = 1) : d1177 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9626 p hg
    simpa only [d4148, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9628 (p : Pattern) (guard : d4148 p = 1) : d1225 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1225, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9627 p hg
    simpa only [d1225, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1225, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d1225, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9629 (p : Pattern) (guard : d4148 p = 1) : d1226 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1226, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1226, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1226, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1226, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9630 (p : Pattern) (guard : d4148 p = 1) : d1227 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1227, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9629 p hg
    simpa only [d1227, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1227, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9593 p hg
    simpa only [d1227, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9631 (p : Pattern) (guard : d4149 p = 1) : d1228 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9625 p hg
    simpa only [d4149, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9630 p hg
    simpa only [d4149, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9632 (p : Pattern) (guard : d4149 p = 1) : d1229 p ≤ (2 : Int) + d4797 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1229, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9624 p hg
    simpa only [d1229, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1229, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9631 p hg
    simpa only [d1229, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9633 (p : Pattern) (guard : d0 p = 1) : d1232 p ≤ (2 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9634 (p : Pattern) (guard : d4149 p = 1) : d1233 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9633 p hg
    simpa only [d4149, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9630 p hg
    simpa only [d4149, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9635 (p : Pattern) (guard : d4149 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare9636 (p : Pattern) (guard : d4149 p = 1) : d1234 p ≤ (2 : Int) + d4800 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1234, d4800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9634 p hg
    simpa only [d1234, d4800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1234, d4800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1234, d4800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9637 (p : Pattern) (guard : d4149 p = 1) : d1235 p ≤ (2 : Int) + d4801 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1235, d4801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9632 p hg
    simpa only [d1235, d4801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1235, d4801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9636 p hg
    simpa only [d1235, d4801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9638 (p : Pattern) (guard : d4149 p = 1) : d1236 p ≤ (2 : Int) + d4802 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1236, d4802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9613 p hg
    simpa only [d1236, d4802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1236, d4802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9637 p hg
    simpa only [d1236, d4802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9639 (p : Pattern) (guard : d0 p = 1) : d1244 p ≤ (2 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9640 (p : Pattern) (guard : d0 p = 1) : d368 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9641 (p : Pattern) (guard : d4148 p = 1) : d1208 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9640 p hg
    simpa only [d4148, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9642 (p : Pattern) (guard : d4148 p = 1) : d1245 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1245, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9641 p hg
    simpa only [d1245, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1245, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9565 p hg
    simpa only [d1245, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9643 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9644 (p : Pattern) (guard : d4148 p = 1) : d1170 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d4148, d1170, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9643 p hg
    simpa only [d4148, d1170, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9645 (p : Pattern) (guard : d4148 p = 1) : d1246 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1246, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9644 p hg
    simpa only [d1246, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1246, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9566 p hg
    simpa only [d1246, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9646 (p : Pattern) (guard : d4148 p = 1) : d1247 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1247, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9642 p hg
    simpa only [d1247, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1247, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9645 p hg
    simpa only [d1247, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9647 (p : Pattern) (guard : d4148 p = 1) : d1248 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1248, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9646 p hg
    simpa only [d1248, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1248, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9622 p hg
    simpa only [d1248, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9648 (p : Pattern) (guard : d4149 p = 1) : d1249 p ≤ (2 : Int) + d52 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9639 p hg
    simpa only [d4149, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9647 p hg
    simpa only [d4149, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9649 (p : Pattern) (guard : d0 p = 1) : d1252 p ≤ (2 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9650 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9651 (p : Pattern) (guard : d4148 p = 1) : d1193 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9650 p hg
    simpa only [d4148, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9652 (p : Pattern) (guard : d4148 p = 1) : d1253 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1253, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9651 p hg
    simpa only [d1253, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1253, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d1253, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9653 (p : Pattern) (guard : d4148 p = 1) : d1254 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1254, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9652 p hg
    simpa only [d1254, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1254, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1254, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9654 (p : Pattern) (guard : d4148 p = 1) : d1255 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1255, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9653 p hg
    simpa only [d1255, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1255, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9593 p hg
    simpa only [d1255, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9655 (p : Pattern) (guard : d4149 p = 1) : d1256 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9649 p hg
    simpa only [d4149, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9654 p hg
    simpa only [d4149, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9656 (p : Pattern) (guard : d4149 p = 1) : d1257 p ≤ (2 : Int) + d4797 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1257, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9648 p hg
    simpa only [d1257, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1257, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9655 p hg
    simpa only [d1257, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9657 (p : Pattern) (guard : d4149 p = 1) : d1258 p ≤ (2 : Int) + d4798 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1258, d4798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9595 p hg
    simpa only [d1258, d4798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1258, d4798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9611 p hg
    simpa only [d1258, d4798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9658 (p : Pattern) (guard : d4149 p = 1) : d1259 p ≤ (2 : Int) + d4799 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1259, d4799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9656 p hg
    simpa only [d1259, d4799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1259, d4799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9657 p hg
    simpa only [d1259, d4799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9659 (p : Pattern) (guard : d0 p = 1) : d1260 p ≤ (2 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
