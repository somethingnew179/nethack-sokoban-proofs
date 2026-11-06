/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons074
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10500 (p : Pattern) (guard : d4672 p = 1) : d1285 p ≤ (0 : Int) + d862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10497 p hg
    simpa only [d4672, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10499 p hg
    simpa only [d4672, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10501 (p : Pattern) (guard : d0 p = 1) : d1287 p ≤ (0 : Int) + d862 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10502 (p : Pattern) (guard : d4673 p = 1) : d1288 p ≤ (0 : Int) + d862 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10500 p hg
    simpa only [d4673, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10501 p hg
    simpa only [d4673, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10503 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d1053 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10504 (p : Pattern) (guard : d4672 p = 1) : d1291 p ≤ (0 : Int) + d1053 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10503 p hg
    simpa only [d4672, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9955 p hg
    simpa only [d4672, d1291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10505 (p : Pattern) (guard : d0 p = 1) : d1292 p ≤ (0 : Int) + d1053 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10506 (p : Pattern) (guard : d4673 p = 1) : d1293 p ≤ (0 : Int) + d1053 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10504 p hg
    simpa only [d4673, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10505 p hg
    simpa only [d4673, d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10507 (p : Pattern) (guard : d4673 p = 1) : d1294 p ≤ (0 : Int) + d4831 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1294, d4831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10502 p hg
    simpa only [d1294, d4831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1294, d4831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10506 p hg
    simpa only [d1294, d4831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10508 (p : Pattern) (guard : d4673 p = 1) : d1295 p ≤ (0 : Int) + d4832 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1295, d4832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10496 p hg
    simpa only [d1295, d4832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1295, d4832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10507 p hg
    simpa only [d1295, d4832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10509 (p : Pattern) (guard : d0 p = 1) : d1274 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10510 (p : Pattern) (guard : d4672 p = 1) : d1297 p ≤ (0 : Int) + d133 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10509 p hg
    simpa only [d4672, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d4672, d1297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10511 (p : Pattern) (guard : d0 p = 1) : d1298 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10512 (p : Pattern) (guard : d4673 p = 1) : d1299 p ≤ (0 : Int) + d133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10510 p hg
    simpa only [d4673, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10511 p hg
    simpa only [d4673, d1299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10513 (p : Pattern) (guard : d4672 p = 1) : d1300 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d4672, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d4672, d1300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10514 (p : Pattern) (guard : d4673 p = 1) : d1301 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10513 p hg
    simpa only [d4673, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4673, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10515 (p : Pattern) (guard : d4673 p = 1) : d1302 p ≤ (0 : Int) + d4833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1302, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10512 p hg
    simpa only [d1302, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1302, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1302, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10516 (p : Pattern) (guard : d0 p = 1) : d1303 p ≤ (0 : Int) + d873 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10517 (p : Pattern) (guard : d4672 p = 1) : d1304 p ≤ (0 : Int) + d873 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10516 p hg
    simpa only [d4672, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d4672, d1304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10518 (p : Pattern) (guard : d0 p = 1) : d1300 p ≤ (0 : Int) + d873 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10519 (p : Pattern) (guard : d4673 p = 1) : d1305 p ≤ (0 : Int) + d873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10517 p hg
    simpa only [d4673, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10518 p hg
    simpa only [d4673, d1305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10520 (p : Pattern) (guard : d4673 p = 1) : d1306 p ≤ (0 : Int) + d4834 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1306, d4834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10519 p hg
    simpa only [d1306, d4834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1306, d4834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1306, d4834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10521 (p : Pattern) (guard : d4673 p = 1) : d1307 p ≤ (0 : Int) + d4835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1307, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10515 p hg
    simpa only [d1307, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1307, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10520 p hg
    simpa only [d1307, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10522 (p : Pattern) (guard : d4673 p = 1) : d1308 p ≤ (0 : Int) + d4836 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1308, d4836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10508 p hg
    simpa only [d1308, d4836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1308, d4836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10521 p hg
    simpa only [d1308, d4836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10523 (p : Pattern) (guard : d0 p = 1) : d1272 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10524 (p : Pattern) (guard : d4672 p = 1) : d1309 p ≤ (0 : Int) + d133 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10523 p hg
    simpa only [d4672, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d4672, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10525 (p : Pattern) (guard : d4673 p = 1) : d1310 p ≤ (0 : Int) + d133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10524 p hg
    simpa only [d4673, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10511 p hg
    simpa only [d4673, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10526 (p : Pattern) (guard : d4673 p = 1) : d1311 p ≤ (0 : Int) + d4833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1311, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10525 p hg
    simpa only [d1311, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1311, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1311, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10527 (p : Pattern) (guard : d0 p = 1) : d1312 p ≤ (0 : Int) + d873 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10528 (p : Pattern) (guard : d4672 p = 1) : d1313 p ≤ (0 : Int) + d873 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10527 p hg
    simpa only [d4672, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d4672, d1313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10529 (p : Pattern) (guard : d4673 p = 1) : d1314 p ≤ (0 : Int) + d873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10528 p hg
    simpa only [d4673, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10518 p hg
    simpa only [d4673, d1314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10530 (p : Pattern) (guard : d4673 p = 1) : d1315 p ≤ (0 : Int) + d4834 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1315, d4834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10529 p hg
    simpa only [d1315, d4834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1315, d4834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1315, d4834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10531 (p : Pattern) (guard : d4673 p = 1) : d1316 p ≤ (0 : Int) + d4835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1316, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10526 p hg
    simpa only [d1316, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1316, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10530 p hg
    simpa only [d1316, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10532 (p : Pattern) (guard : d4672 p = 1) : d159 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d4672, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10533 (p : Pattern) (guard : d4673 p = 1) : d160 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10532 p hg
    simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4673, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10534 (p : Pattern) (guard : d4673 p = 1) : d161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10533 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10535 (p : Pattern) (guard : d4673 p = 1) : d162 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10534 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10536 (p : Pattern) (guard : d4673 p = 1) : d1317 p ≤ (0 : Int) + d4837 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1317, d4837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10531 p hg
    simpa only [d1317, d4837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1317, d4837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10535 p hg
    simpa only [d1317, d4837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10537 (p : Pattern) (guard : d4673 p = 1) : d1318 p ≤ (0 : Int) + d4838 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1318, d4838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10522 p hg
    simpa only [d1318, d4838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1318, d4838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10536 p hg
    simpa only [d1318, d4838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10538 (p : Pattern) (guard : d0 p = 1) : d1319 p ≤ (0 : Int) + d1043 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10539 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10540 (p : Pattern) (guard : d4148 p = 1) : d1303 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1303, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1303, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1303, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10539 p hg
    simpa only [d4148, d1303, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10541 (p : Pattern) (guard : d4672 p = 1) : d1320 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10538 p hg
    simpa only [d4672, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10540 p hg
    simpa only [d4672, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10542 (p : Pattern) (guard : d0 p = 1) : d1298 p ≤ (0 : Int) + d1043 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10543 (p : Pattern) (guard : d4673 p = 1) : d1321 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10541 p hg
    simpa only [d4673, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10542 p hg
    simpa only [d4673, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10544 (p : Pattern) (guard : d0 p = 1) : d1322 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10545 (p : Pattern) (guard : d4672 p = 1) : d1323 p ≤ (0 : Int) + d126 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10544 p hg
    simpa only [d4672, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d4672, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10546 (p : Pattern) (guard : d4673 p = 1) : d1324 p ≤ (0 : Int) + d126 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10545 p hg
    simpa only [d4673, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10494 p hg
    simpa only [d4673, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10547 (p : Pattern) (guard : d4673 p = 1) : d1325 p ≤ (0 : Int) + d4830 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1325, d4830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10543 p hg
    simpa only [d1325, d4830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1325, d4830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10546 p hg
    simpa only [d1325, d4830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10548 (p : Pattern) (guard : d0 p = 1) : d1274 p ≤ (0 : Int) + d862 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10549 (p : Pattern) (guard : d4672 p = 1) : d1326 p ≤ (0 : Int) + d862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10548 p hg
    simpa only [d4672, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d4672, d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10550 (p : Pattern) (guard : d0 p = 1) : d1300 p ≤ (0 : Int) + d862 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10551 (p : Pattern) (guard : d4673 p = 1) : d1327 p ≤ (0 : Int) + d862 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10549 p hg
    simpa only [d4673, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10550 p hg
    simpa only [d4673, d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10552 (p : Pattern) (guard : d4673 p = 1) : d1328 p ≤ (0 : Int) + d4831 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1328, d4831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10551 p hg
    simpa only [d1328, d4831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1328, d4831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10506 p hg
    simpa only [d1328, d4831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10553 (p : Pattern) (guard : d4673 p = 1) : d1329 p ≤ (0 : Int) + d4832 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1329, d4832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10547 p hg
    simpa only [d1329, d4832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1329, d4832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10552 p hg
    simpa only [d1329, d4832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10554 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10555 (p : Pattern) (guard : d4672 p = 1) : d1296 p ≤ (0 : Int) + d133 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10554 p hg
    simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10556 (p : Pattern) (guard : d4673 p = 1) : d1330 p ≤ (0 : Int) + d133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10555 p hg
    simpa only [d4673, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10511 p hg
    simpa only [d4673, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10557 (p : Pattern) (guard : d4673 p = 1) : d1331 p ≤ (0 : Int) + d4833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1331, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10556 p hg
    simpa only [d1331, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1331, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1331, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10558 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d873 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10559 (p : Pattern) (guard : d4672 p = 1) : d1332 p ≤ (0 : Int) + d873 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10558 p hg
    simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10560 (p : Pattern) (guard : d4673 p = 1) : d1333 p ≤ (0 : Int) + d873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10559 p hg
    simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10518 p hg
    simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10561 (p : Pattern) (guard : d4673 p = 1) : d1334 p ≤ (0 : Int) + d4834 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1334, d4834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10560 p hg
    simpa only [d1334, d4834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1334, d4834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1334, d4834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10562 (p : Pattern) (guard : d4673 p = 1) : d1335 p ≤ (0 : Int) + d4835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1335, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10557 p hg
    simpa only [d1335, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1335, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10561 p hg
    simpa only [d1335, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10563 (p : Pattern) (guard : d4673 p = 1) : d1336 p ≤ (0 : Int) + d4836 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1336, d4836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10553 p hg
    simpa only [d1336, d4836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1336, d4836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10562 p hg
    simpa only [d1336, d4836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10564 (p : Pattern) (guard : d0 p = 1) : d1303 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10565 (p : Pattern) (guard : d4672 p = 1) : d1337 p ≤ (0 : Int) + d133 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10564 p hg
    simpa only [d4672, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d4672, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10566 (p : Pattern) (guard : d4673 p = 1) : d1338 p ≤ (0 : Int) + d133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10565 p hg
    simpa only [d4673, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10511 p hg
    simpa only [d4673, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10567 (p : Pattern) (guard : d4673 p = 1) : d1339 p ≤ (0 : Int) + d4833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1339, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10566 p hg
    simpa only [d1339, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1339, d4833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1339, d4833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10568 (p : Pattern) (guard : d4673 p = 1) : d1340 p ≤ (0 : Int) + d4835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1340, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10567 p hg
    simpa only [d1340, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1340, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10561 p hg
    simpa only [d1340, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10569 (p : Pattern) (guard : d4673 p = 1) : d1341 p ≤ (0 : Int) + d4837 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1341, d4837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10568 p hg
    simpa only [d1341, d4837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1341, d4837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d1341, d4837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10570 (p : Pattern) (guard : d4673 p = 1) : d1342 p ≤ (0 : Int) + d4838 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1342, d4838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10563 p hg
    simpa only [d1342, d4838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1342, d4838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10569 p hg
    simpa only [d1342, d4838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10571 (p : Pattern) (guard : d4673 p = 1) : d1343 p ≤ (0 : Int) + d4838 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10537 p hg
    simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10570 p hg
    simpa only [d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10572 (p : Pattern) (guard : d4673 p = 1) : d1344 p ≤ (0 : Int) + d4839 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1344, d4839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10439 p hg
    simpa only [d1344, d4839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1344, d4839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10571 p hg
    simpa only [d1344, d4839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10573 (p : Pattern) (guard : d4673 p = 1) : d1345 p ≤ (0 : Int) + d4840 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1345, d4840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10485 p hg
    simpa only [d1345, d4840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1345, d4840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10572 p hg
    simpa only [d1345, d4840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10574 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10575 (p : Pattern) (guard : d4672 p = 1) : d1181 p ≤ (0 : Int) + d808 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10574 p hg
    simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d4672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10576 (p : Pattern) (guard : d4673 p = 1) : d1346 p ≤ (0 : Int) + d808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10575 p hg
    simpa only [d4673, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d4673, d1346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10577 (p : Pattern) (guard : d0 p = 1) : d1347 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10578 (p : Pattern) (guard : d4672 p = 1) : d1348 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10577 p hg
    simpa only [d4672, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d4672, d1348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10579 (p : Pattern) (guard : d4673 p = 1) : d1349 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10578 p hg
    simpa only [d4673, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4673, d1349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10580 (p : Pattern) (guard : d4673 p = 1) : d1350 p ≤ (0 : Int) + d4822 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1350, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10576 p hg
    simpa only [d1350, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1350, d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10579 p hg
    simpa only [d1350, d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10581 (p : Pattern) (guard : d4673 p = 1) : d1351 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1351, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10479 p hg
    simpa only [d1351, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1351, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10580 p hg
    simpa only [d1351, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10582 (p : Pattern) (guard : d4673 p = 1) : d1352 p ≤ (0 : Int) + d4824 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1352, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10475 p hg
    simpa only [d1352, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1352, d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10581 p hg
    simpa only [d1352, d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10583 (p : Pattern) (guard : d4673 p = 1) : d1353 p ≤ (0 : Int) + d4823 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1353, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10425 p hg
    simpa only [d1353, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1353, d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10580 p hg
    simpa only [d1353, d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10584 (p : Pattern) (guard : d4673 p = 1) : d1354 p ≤ (0 : Int) + d4827 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1354, d4827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10583 p hg
    simpa only [d1354, d4827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1354, d4827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d1354, d4827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10585 (p : Pattern) (guard : d4673 p = 1) : d1355 p ≤ (0 : Int) + d4828 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1355, d4828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10582 p hg
    simpa only [d1355, d4828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1355, d4828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10584 p hg
    simpa only [d1355, d4828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10586 (p : Pattern) (guard : d4673 p = 1) : d1356 p ≤ (0 : Int) + d4829 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1356, d4829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10465 p hg
    simpa only [d1356, d4829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1356, d4829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10585 p hg
    simpa only [d1356, d4829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10587 (p : Pattern) (guard : d4673 p = 1) : d1357 p ≤ (0 : Int) + d4829 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10439 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10586 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10588 (p : Pattern) (guard : d4672 p = 1) : d1358 p ≤ (0 : Int) + d862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10497 p hg
    simpa only [d4672, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d4672, d1358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10589 (p : Pattern) (guard : d4673 p = 1) : d1359 p ≤ (0 : Int) + d862 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10588 p hg
    simpa only [d4673, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10550 p hg
    simpa only [d4673, d1359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10590 (p : Pattern) (guard : d4673 p = 1) : d1360 p ≤ (0 : Int) + d4831 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1360, d4831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10589 p hg
    simpa only [d1360, d4831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1360, d4831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10506 p hg
    simpa only [d1360, d4831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10591 (p : Pattern) (guard : d4673 p = 1) : d1361 p ≤ (0 : Int) + d4832 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1361, d4832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10496 p hg
    simpa only [d1361, d4832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1361, d4832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10590 p hg
    simpa only [d1361, d4832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10592 (p : Pattern) (guard : d4673 p = 1) : d1362 p ≤ (0 : Int) + d4835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1362, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10515 p hg
    simpa only [d1362, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1362, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10561 p hg
    simpa only [d1362, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10593 (p : Pattern) (guard : d4673 p = 1) : d1363 p ≤ (0 : Int) + d4836 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1363, d4836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10591 p hg
    simpa only [d1363, d4836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1363, d4836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10592 p hg
    simpa only [d1363, d4836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10594 (p : Pattern) (guard : d4673 p = 1) : d1364 p ≤ (0 : Int) + d4835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1364, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10526 p hg
    simpa only [d1364, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1364, d4835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10561 p hg
    simpa only [d1364, d4835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10595 (p : Pattern) (guard : d4673 p = 1) : d1365 p ≤ (0 : Int) + d4837 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1365, d4837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10594 p hg
    simpa only [d1365, d4837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1365, d4837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10535 p hg
    simpa only [d1365, d4837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10596 (p : Pattern) (guard : d4673 p = 1) : d1366 p ≤ (0 : Int) + d4838 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1366, d4838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10593 p hg
    simpa only [d1366, d4838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1366, d4838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10595 p hg
    simpa only [d1366, d4838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10597 (p : Pattern) (guard : d0 p = 1) : d1319 p ≤ (0 : Int) + d291 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10598 (p : Pattern) (guard : d4672 p = 1) : d1367 p ≤ (0 : Int) + d291 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10597 p hg
    simpa only [d4672, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9543 p hg
    simpa only [d4672, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10599 (p : Pattern) (guard : d0 p = 1) : d1298 p ≤ (0 : Int) + d291 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10600 (p : Pattern) (guard : d4673 p = 1) : d1368 p ≤ (0 : Int) + d291 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10598 p hg
    simpa only [d4673, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10599 p hg
    simpa only [d4673, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10601 (p : Pattern) (guard : d0 p = 1) : d1369 p ≤ (0 : Int) + d275 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10602 (p : Pattern) (guard : d4672 p = 1) : d1371 p ≤ (0 : Int) + d275 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10601 p hg
    simpa only [d4672, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d4672, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10603 (p : Pattern) (guard : d0 p = 1) : d1372 p ≤ (0 : Int) + d275 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10604 (p : Pattern) (guard : d4673 p = 1) : d1373 p ≤ (0 : Int) + d275 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10602 p hg
    simpa only [d4673, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10603 p hg
    simpa only [d4673, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10605 (p : Pattern) (guard : d4673 p = 1) : d1374 p ≤ (0 : Int) + d4841 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1374, d4841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10600 p hg
    simpa only [d1374, d4841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1374, d4841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10604 p hg
    simpa only [d1374, d4841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10606 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d925 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10607 (p : Pattern) (guard : d4672 p = 1) : d1332 p ≤ (0 : Int) + d925 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10606 p hg
    simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10049 p hg
    simpa only [d4672, d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10608 (p : Pattern) (guard : d0 p = 1) : d1300 p ≤ (0 : Int) + d925 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10609 (p : Pattern) (guard : d4673 p = 1) : d1333 p ≤ (0 : Int) + d925 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10607 p hg
    simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10608 p hg
    simpa only [d4673, d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10610 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d1128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10611 (p : Pattern) (guard : d4672 p = 1) : d1376 p ≤ (0 : Int) + d1128 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10610 p hg
    simpa only [d4672, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10055 p hg
    simpa only [d4672, d1376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10612 (p : Pattern) (guard : d0 p = 1) : d1377 p ≤ (0 : Int) + d1128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10613 (p : Pattern) (guard : d4673 p = 1) : d1378 p ≤ (0 : Int) + d1128 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10611 p hg
    simpa only [d4673, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10612 p hg
    simpa only [d4673, d1378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10614 (p : Pattern) (guard : d4673 p = 1) : d1379 p ≤ (0 : Int) + d4842 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1379, d4842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10609 p hg
    simpa only [d1379, d4842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1379, d4842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10613 p hg
    simpa only [d1379, d4842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10615 (p : Pattern) (guard : d4673 p = 1) : d1380 p ≤ (0 : Int) + d4843 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1380, d4843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10605 p hg
    simpa only [d1380, d4843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1380, d4843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10614 p hg
    simpa only [d1380, d4843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10616 (p : Pattern) (guard : d0 p = 1) : d1296 p ≤ (0 : Int) + d1133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10617 (p : Pattern) (guard : d4672 p = 1) : d1381 p ≤ (0 : Int) + d1133 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10616 p hg
    simpa only [d4672, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10061 p hg
    simpa only [d4672, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10618 (p : Pattern) (guard : d0 p = 1) : d1382 p ≤ (0 : Int) + d1133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10619 (p : Pattern) (guard : d4673 p = 1) : d1383 p ≤ (0 : Int) + d1133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10617 p hg
    simpa only [d4673, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10618 p hg
    simpa only [d4673, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10620 (p : Pattern) (guard : d4673 p = 1) : d1384 p ≤ (0 : Int) + d4844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1384, d4844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10619 p hg
    simpa only [d1384, d4844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1384, d4844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1384, d4844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10621 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d1137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10622 (p : Pattern) (guard : d4672 p = 1) : d1386 p ≤ (0 : Int) + d1137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10621 p hg
    simpa only [d4672, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10067 p hg
    simpa only [d4672, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10623 (p : Pattern) (guard : d0 p = 1) : d1387 p ≤ (0 : Int) + d1137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10624 (p : Pattern) (guard : d4673 p = 1) : d1388 p ≤ (0 : Int) + d1137 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10622 p hg
    simpa only [d4673, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10623 p hg
    simpa only [d4673, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10625 (p : Pattern) (guard : d4672 p = 1) : d213 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6619 p hg
    simpa only [d4672, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d4672, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10626 (p : Pattern) (guard : d4673 p = 1) : d1389 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10625 p hg
    simpa only [d4673, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4673, d1389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10627 (p : Pattern) (guard : d4673 p = 1) : d1390 p ≤ (0 : Int) + d4845 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1390, d4845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10624 p hg
    simpa only [d1390, d4845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1390, d4845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10626 p hg
    simpa only [d1390, d4845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10628 (p : Pattern) (guard : d4673 p = 1) : d1391 p ≤ (0 : Int) + d4846 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1391, d4846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10620 p hg
    simpa only [d1391, d4846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1391, d4846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10627 p hg
    simpa only [d1391, d4846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10629 (p : Pattern) (guard : d4673 p = 1) : d1392 p ≤ (0 : Int) + d4847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1392, d4847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10615 p hg
    simpa only [d1392, d4847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1392, d4847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10628 p hg
    simpa only [d1392, d4847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10630 (p : Pattern) (guard : d4673 p = 1) : d1393 p ≤ (0 : Int) + d4848 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1393, d4848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10628 p hg
    simpa only [d1393, d4848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1393, d4848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d1393, d4848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10631 (p : Pattern) (guard : d4673 p = 1) : d1394 p ≤ (0 : Int) + d4849 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1394, d4849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10629 p hg
    simpa only [d1394, d4849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1394, d4849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10630 p hg
    simpa only [d1394, d4849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10632 (p : Pattern) (guard : d4673 p = 1) : d1395 p ≤ (0 : Int) + d4850 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1395, d4850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10596 p hg
    simpa only [d1395, d4850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1395, d4850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10631 p hg
    simpa only [d1395, d4850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10633 (p : Pattern) (guard : d4673 p = 1) : d1396 p ≤ (0 : Int) + d4851 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1396, d4851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10439 p hg
    simpa only [d1396, d4851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1396, d4851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d1396, d4851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10634 (p : Pattern) (guard : d4673 p = 1) : d1397 p ≤ (0 : Int) + d4852 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1397, d4852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10587 p hg
    simpa only [d1397, d4852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1397, d4852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d1397, d4852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10635 (p : Pattern) (guard : d4673 p = 1) : d1398 p ≤ (0 : Int) + d4853 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d1398, d4853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10573 p hg
    simpa only [d1398, d4853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d1398, d4853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d1398, d4853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10636 (p : Pattern) (guard : d1 p = 1) : d1503 p ≤ (0 : Int) + d1503 p := by
  omega
theorem compare10637 (p : Pattern) (guard : d4148 p = 1) : d1399 p ≤ (0 : Int) + d1155 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8046 p hg
    simpa only [d1399, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1399, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1399, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10638 (p : Pattern) (guard : d4148 p = 1) : d1400 p ≤ (0 : Int) + d1156 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3617 p hg
    simpa only [d1400, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1400, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d1400, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10639 (p : Pattern) (guard : d4148 p = 1) : d1401 p ≤ (0 : Int) + d1159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1401, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8050 p hg
    simpa only [d1401, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1401, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d1401, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
