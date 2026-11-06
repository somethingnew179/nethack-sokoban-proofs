/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1400 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d122, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1401 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1398 p hg
    simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1400 p hg
    simpa only [d123, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1402 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1401 p hg
    simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1329 p hg
    simpa only [d127, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1403 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d7 p := by
  change (1 : Int) ≤ (0 : Int) + 7
  decide
theorem compare1404 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1405 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1404 p hg
    simpa only [d103, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1406 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d124, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1407 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d126, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1408 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1407 p hg
    simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d129, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1409 (p : Pattern) (guard : d1 p = 1) : d130 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1408 p hg
    simpa only [d130, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1410 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1409 p hg
    simpa only [d131, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1411 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (0 : Int) + d214 p := by
  omega
theorem compare1412 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d122, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1413 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d139, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1414 (p : Pattern) (guard : d1 p = 1) : d140 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1412 p hg
    simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1413 p hg
    simpa only [d140, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1415 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d7 p := by
  change (5 : Int) ≤ (0 : Int) + 7
  decide
theorem compare1416 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d106, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1417 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1416 p hg
    simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1418 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d125, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1419 (p : Pattern) (guard : d1 p = 1) : d215 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d215, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1418 p hg
    simpa only [d215, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d215, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d215, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1420 (p : Pattern) (guard : d1 p = 1) : d216 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d216, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1414 p hg
    simpa only [d216, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d216, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1419 p hg
    simpa only [d216, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1421 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d9 p := by
  change (5 : Int) ≤ (0 : Int) + 9
  decide
theorem compare1422 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1423 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1422 p hg
    simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1424 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1423 p hg
    simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d125, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1425 (p : Pattern) (guard : d1 p = 1) : d215 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d215, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1424 p hg
    simpa only [d215, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d215, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d215, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1426 (p : Pattern) (guard : d1 p = 1) : d217 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d217, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1425 p hg
    simpa only [d217, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d217, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d217, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1427 (p : Pattern) (guard : d1 p = 1) : d218 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d218, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1420 p hg
    simpa only [d218, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d218, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1426 p hg
    simpa only [d218, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1428 (p : Pattern) (guard : d1 p = 1) : d219 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d219, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d219, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d219, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1427 p hg
    simpa only [d219, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1429 (p : Pattern) (guard : d1 p = 1) : d220 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d220, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1410 p hg
    simpa only [d220, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d220, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1428 p hg
    simpa only [d220, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1430 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1269 p hg
    simpa only [d110, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1431 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1430 p hg
    simpa only [d111, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1432 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1431 p hg
    simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1272 p hg
    simpa only [d114, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1433 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1432 p hg
    simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d152, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1434 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d132 p := by
  omega
theorem compare1435 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (0 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1436 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (0 : Int) + d211 p := by
  omega
theorem compare1437 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d212, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1435 p hg
    simpa only [d212, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d212, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1436 p hg
    simpa only [d212, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1438 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d108, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1439 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1438 p hg
    simpa only [d109, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1440 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d211, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d211, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1441 (p : Pattern) (guard : d1 p = 1) : d213 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d213, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1440 p hg
    simpa only [d213, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d213, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d213, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1442 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d214, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1437 p hg
    simpa only [d214, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d214, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1441 p hg
    simpa only [d214, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1443 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d9 p := by
  change (7 : Int) ≤ (0 : Int) + 9
  decide
theorem compare1444 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1445 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1444 p hg
    simpa only [d120, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1446 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1445 p hg
    simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d121, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1447 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1445 p hg
    simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1446 p hg
    simpa only [d148, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1448 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d153, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1449 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1448 p hg
    simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d154, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1450 (p : Pattern) (guard : d1 p = 1) : d155 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1449 p hg
    simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d155, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1451 (p : Pattern) (guard : d1 p = 1) : d221 p ≤ (0 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d221, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1442 p hg
    simpa only [d221, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d221, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d221, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1452 (p : Pattern) (guard : d1 p = 1) : d222 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d222, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1433 p hg
    simpa only [d222, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d222, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d222, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1453 (p : Pattern) (guard : d1 p = 1) : d223 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1429 p hg
    simpa only [d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1452 p hg
    simpa only [d223, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1454 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1423 p hg
    simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d108, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1455 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1423 p hg
    simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1454 p hg
    simpa only [d109, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1456 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1455 p hg
    simpa only [d110, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1457 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1456 p hg
    simpa only [d111, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1458 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1257 p hg
    simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1455 p hg
    simpa only [d110, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1459 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (0 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1458 p hg
    simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d113, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1460 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1457 p hg
    simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1459 p hg
    simpa only [d114, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1461 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d11 p := by
  change (7 : Int) ≤ (0 : Int) + 11
  decide
theorem compare1462 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1463 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1462 p hg
    simpa only [d120, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1464 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d121, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1465 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d148, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1466 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1298 p hg
    simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1465 p hg
    simpa only [d149, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1467 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1466 p hg
    simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d150, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1468 (p : Pattern) (guard : d1 p = 1) : d151 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1467 p hg
    simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d151, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1469 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1460 p hg
    simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1468 p hg
    simpa only [d152, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1470 (p : Pattern) (guard : d1 p = 1) : d222 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d222, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1469 p hg
    simpa only [d222, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d222, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d222, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1471 (p : Pattern) (guard : d1 p = 1) : d224 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d224, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1470 p hg
    simpa only [d224, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d224, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1384 p hg
    simpa only [d224, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1472 (p : Pattern) (guard : d1 p = 1) : d225 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d225, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d225, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d225, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d225, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1473 (p : Pattern) (guard : d0 p = 1) : d263 p ≤ (0 : Int) + d263 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1474 (p : Pattern) (guard : d4058 p = 1) : d264 p ≤ (0 : Int) + d263 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1472 p hg
    simpa only [d4058, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1473 p hg
    simpa only [d4058, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1475 (p : Pattern) (guard : d4058 p = 1) : d265 p ≤ (0 : Int) + d4100 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d265, d4100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d265, d4100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d265, d4100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1474 p hg
    simpa only [d265, d4100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1476 (p : Pattern) (guard : d4058 p = 1) : d266 p ≤ (0 : Int) + d4101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d266, d4101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1395 p hg
    simpa only [d266, d4101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d266, d4101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1475 p hg
    simpa only [d266, d4101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1477 (p : Pattern) (guard : d4058 p = 1) : d267 p ≤ (0 : Int) + d4102 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d267, d4102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1390 p hg
    simpa only [d267, d4102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d267, d4102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1476 p hg
    simpa only [d267, d4102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1478 (p : Pattern) (guard : d0 p = 1) : d208 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1479 (p : Pattern) (guard : d4058 p = 1) : d209 p ≤ (0 : Int) + d490 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d209, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d209, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d209, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1478 p hg
    simpa only [d4058, d209, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1480 (p : Pattern) (guard : d4058 p = 1) : d210 p ≤ (0 : Int) + d491 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d210, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1099 p hg
    simpa only [d210, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d210, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1479 p hg
    simpa only [d210, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1481 (p : Pattern) (guard : d0 p = 1) : d263 p ≤ (0 : Int) + d477 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1482 (p : Pattern) (guard : d4058 p = 1) : d264 p ≤ (0 : Int) + d495 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d264, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d4058, d264, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d264, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d4058, d264, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1483 (p : Pattern) (guard : d4058 p = 1) : d265 p ≤ (0 : Int) + d496 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d265, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1099 p hg
    simpa only [d265, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d265, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1482 p hg
    simpa only [d265, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1484 (p : Pattern) (guard : d4058 p = 1) : d266 p ≤ (0 : Int) + d497 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d266, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1480 p hg
    simpa only [d266, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d266, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1483 p hg
    simpa only [d266, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1485 (p : Pattern) (guard : d4058 p = 1) : d267 p ≤ (0 : Int) + d498 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d267, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d267, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d267, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1484 p hg
    simpa only [d267, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1486 (p : Pattern) (guard : d0 p = 1) : d98 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1487 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) ≤ (0 : Int) + 6
  decide
theorem compare1488 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1489 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1490 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d37, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare784 p hg
    simpa only [d37, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1491 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare783 p hg
    simpa only [d38, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1490 p hg
    simpa only [d38, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1492 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) ≤ (0 : Int) + 11
  decide
theorem compare1493 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1494 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1495 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d42, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d42, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1496 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1495 p hg
    simpa only [d44, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d44, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1497 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1491 p hg
    simpa only [d45, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1496 p hg
    simpa only [d45, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1498 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare1499 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1500 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1501 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1502 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1501 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1503 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1502 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare910 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1504 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1497 p hg
    simpa only [d51, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1503 p hg
    simpa only [d51, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1505 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d52, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1504 p hg
    simpa only [d52, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1506 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d12 p := by
  change (2 : Int) ≤ (0 : Int) + 12
  decide
theorem compare1507 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1508 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1509 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1510 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1490 p hg
    simpa only [d67, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1509 p hg
    simpa only [d67, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1511 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1512 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1510 p hg
    simpa only [d69, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1511 p hg
    simpa only [d69, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1513 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1514 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1513 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1515 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1512 p hg
    simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1514 p hg
    simpa only [d75, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1516 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d76, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1515 p hg
    simpa only [d76, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1517 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1505 p hg
    simpa only [d77, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1516 p hg
    simpa only [d77, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1518 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) ≤ (0 : Int) + 9
  decide
theorem compare1519 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1520 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1521 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1520 p hg
    simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1522 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1520 p hg
    simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1521 p hg
    simpa only [d16, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1523 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1524 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d16, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d16, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1525 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1522 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1526 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1527 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1526 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1528 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d21, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d21, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1529 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1525 p hg
    simpa only [d22, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1528 p hg
    simpa only [d22, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1530 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1528 p hg
    simpa only [d28, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d28, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1531 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1529 p hg
    simpa only [d29, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1530 p hg
    simpa only [d29, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1532 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d11 p := by
  change (2 : Int) ≤ (0 : Int) + 11
  decide
theorem compare1533 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1534 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1533 p hg
    simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1535 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d32, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1536 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1535 p hg
    simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1537 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1536 p hg
    simpa only [d79, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d79, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1538 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1537 p hg
    simpa only [d80, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d80, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1539 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1538 p hg
    simpa only [d81, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d81, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
