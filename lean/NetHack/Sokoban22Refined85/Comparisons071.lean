/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9940 (p : Pattern) (guard : d4148 p = 1) : d1281 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1281, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9939 p hg
    simpa only [d1281, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1281, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1281, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9941 (p : Pattern) (guard : d4148 p = 1) : d1282 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1282, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9936 p hg
    simpa only [d1282, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1282, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9940 p hg
    simpa only [d1282, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9942 (p : Pattern) (guard : d0 p = 1) : d368 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9943 (p : Pattern) (guard : d4148 p = 1) : d1283 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1283, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1283, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1283, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9942 p hg
    simpa only [d4148, d1283, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9944 (p : Pattern) (guard : d4148 p = 1) : d1284 p ≤ (0 : Int) + d1284 p := by
  omega
theorem compare9945 (p : Pattern) (guard : d4148 p = 1) : d1285 p ≤ (0 : Int) + d1444 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1285, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9943 p hg
    simpa only [d1285, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1285, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9944 p hg
    simpa only [d1285, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9946 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9947 (p : Pattern) (guard : d4148 p = 1) : d1286 p ≤ (0 : Int) + d862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1286, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1286, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1286, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9946 p hg
    simpa only [d4148, d1286, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9948 (p : Pattern) (guard : d4148 p = 1) : d1287 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9947 p hg
    simpa only [d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9949 (p : Pattern) (guard : d4148 p = 1) : d1288 p ≤ (0 : Int) + d1445 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1288, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9945 p hg
    simpa only [d1288, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1288, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9948 p hg
    simpa only [d1288, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9950 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9951 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (0 : Int) + d862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1289, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9950 p hg
    simpa only [d4148, d1289, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9952 (p : Pattern) (guard : d4148 p = 1) : d1290 p ≤ (0 : Int) + d1290 p := by
  omega
theorem compare9953 (p : Pattern) (guard : d4148 p = 1) : d1291 p ≤ (0 : Int) + d1446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1291, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d1291, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1291, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9952 p hg
    simpa only [d1291, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9954 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d229 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9955 (p : Pattern) (guard : d4148 p = 1) : d1290 p ≤ (0 : Int) + d1053 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1290, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8221 p hg
    simpa only [d4148, d1290, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1290, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9954 p hg
    simpa only [d4148, d1290, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9956 (p : Pattern) (guard : d4148 p = 1) : d1292 p ≤ (0 : Int) + d1054 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9955 p hg
    simpa only [d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1292, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9957 (p : Pattern) (guard : d4148 p = 1) : d1293 p ≤ (0 : Int) + d1447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1293, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9953 p hg
    simpa only [d1293, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1293, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9956 p hg
    simpa only [d1293, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9958 (p : Pattern) (guard : d4148 p = 1) : d1294 p ≤ (0 : Int) + d1448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1294, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9949 p hg
    simpa only [d1294, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1294, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9957 p hg
    simpa only [d1294, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9959 (p : Pattern) (guard : d4148 p = 1) : d1295 p ≤ (0 : Int) + d1449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1295, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9941 p hg
    simpa only [d1295, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1295, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9958 p hg
    simpa only [d1295, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9960 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9961 (p : Pattern) (guard : d4148 p = 1) : d1296 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1296, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1296, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1296, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9960 p hg
    simpa only [d4148, d1296, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9962 (p : Pattern) (guard : d4148 p = 1) : d1298 p ≤ (0 : Int) + d1450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1298, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d1298, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1298, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1298, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9963 (p : Pattern) (guard : d4148 p = 1) : d1299 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9461 p hg
    simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9962 p hg
    simpa only [d1299, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9964 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (0 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9960 p hg
    simpa only [d4148, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9965 (p : Pattern) (guard : d4148 p = 1) : d1300 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1300, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9966 (p : Pattern) (guard : d4148 p = 1) : d1301 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9965 p hg
    simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1301, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9967 (p : Pattern) (guard : d4148 p = 1) : d1302 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1302, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9963 p hg
    simpa only [d1302, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1302, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d1302, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9968 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9969 (p : Pattern) (guard : d4148 p = 1) : d1303 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1303, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1303, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1303, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9968 p hg
    simpa only [d4148, d1303, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9970 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (0 : Int) + d1289 p := by
  omega
theorem compare9971 (p : Pattern) (guard : d4148 p = 1) : d1304 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1304, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9969 p hg
    simpa only [d1304, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1304, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1304, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9972 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (0 : Int) + d873 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1289, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d4148, d1289, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9973 (p : Pattern) (guard : d4148 p = 1) : d1300 p ≤ (0 : Int) + d1064 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1300, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9974 (p : Pattern) (guard : d4148 p = 1) : d1305 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1305, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9971 p hg
    simpa only [d1305, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1305, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9973 p hg
    simpa only [d1305, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9975 (p : Pattern) (guard : d4148 p = 1) : d1301 p ≤ (0 : Int) + d1066 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9973 p hg
    simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1301, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9976 (p : Pattern) (guard : d4148 p = 1) : d1306 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1306, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9974 p hg
    simpa only [d1306, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1306, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9975 p hg
    simpa only [d1306, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9977 (p : Pattern) (guard : d4148 p = 1) : d1307 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9967 p hg
    simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9976 p hg
    simpa only [d1307, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9978 (p : Pattern) (guard : d4148 p = 1) : d1308 p ≤ (0 : Int) + d1457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9959 p hg
    simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9977 p hg
    simpa only [d1308, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9979 (p : Pattern) (guard : d4148 p = 1) : d1310 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1310, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9473 p hg
    simpa only [d1310, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1310, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9962 p hg
    simpa only [d1310, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9980 (p : Pattern) (guard : d4148 p = 1) : d1311 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1311, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9979 p hg
    simpa only [d1311, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1311, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d1311, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9981 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9982 (p : Pattern) (guard : d4148 p = 1) : d1312 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1312, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1312, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1312, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9981 p hg
    simpa only [d4148, d1312, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9983 (p : Pattern) (guard : d4148 p = 1) : d1313 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1313, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9982 p hg
    simpa only [d1313, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1313, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1313, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9984 (p : Pattern) (guard : d4148 p = 1) : d1314 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1314, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9983 p hg
    simpa only [d1314, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1314, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9973 p hg
    simpa only [d1314, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9985 (p : Pattern) (guard : d4148 p = 1) : d1315 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1315, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9984 p hg
    simpa only [d1315, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1315, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9975 p hg
    simpa only [d1315, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9986 (p : Pattern) (guard : d4148 p = 1) : d1316 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1316, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9980 p hg
    simpa only [d1316, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1316, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9985 p hg
    simpa only [d1316, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9987 (p : Pattern) (guard : d4148 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare9988 (p : Pattern) (guard : d4148 p = 1) : d1317 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1317, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9986 p hg
    simpa only [d1317, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1317, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9987 p hg
    simpa only [d1317, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9989 (p : Pattern) (guard : d4148 p = 1) : d1318 p ≤ (0 : Int) + d1459 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1318, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9978 p hg
    simpa only [d1318, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1318, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9988 p hg
    simpa only [d1318, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9990 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9991 (p : Pattern) (guard : d4148 p = 1) : d1296 p ≤ (0 : Int) + d1043 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1296, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1296, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1296, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9990 p hg
    simpa only [d4148, d1296, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9992 (p : Pattern) (guard : d4148 p = 1) : d1298 p ≤ (0 : Int) + d1439 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1298, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9991 p hg
    simpa only [d1298, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1298, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1298, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9993 (p : Pattern) (guard : d4148 p = 1) : d1321 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1321, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9484 p hg
    simpa only [d1321, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1321, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9992 p hg
    simpa only [d1321, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9994 (p : Pattern) (guard : d4148 p = 1) : d1322 p ≤ (0 : Int) + d118 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9990 p hg
    simpa only [d4148, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9995 (p : Pattern) (guard : d4148 p = 1) : d1323 p ≤ (0 : Int) + d1441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9994 p hg
    simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1323, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9996 (p : Pattern) (guard : d4148 p = 1) : d1324 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1324, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9995 p hg
    simpa only [d1324, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1324, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1324, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9997 (p : Pattern) (guard : d4148 p = 1) : d1325 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1325, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9993 p hg
    simpa only [d1325, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1325, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9996 p hg
    simpa only [d1325, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9998 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9999 (p : Pattern) (guard : d4148 p = 1) : d1274 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1274, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1274, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1274, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9998 p hg
    simpa only [d4148, d1274, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10000 (p : Pattern) (guard : d4148 p = 1) : d1326 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1326, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9999 p hg
    simpa only [d1326, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1326, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1326, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10001 (p : Pattern) (guard : d4148 p = 1) : d1300 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1300, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10002 (p : Pattern) (guard : d4148 p = 1) : d1327 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1327, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10000 p hg
    simpa only [d1327, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1327, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10001 p hg
    simpa only [d1327, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10003 (p : Pattern) (guard : d4148 p = 1) : d1328 p ≤ (0 : Int) + d1461 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1328, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10002 p hg
    simpa only [d1328, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1328, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9957 p hg
    simpa only [d1328, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10004 (p : Pattern) (guard : d4148 p = 1) : d1329 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1329, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9997 p hg
    simpa only [d1329, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1329, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10003 p hg
    simpa only [d1329, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10005 (p : Pattern) (guard : d4148 p = 1) : d1330 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1330, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9495 p hg
    simpa only [d1330, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1330, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9962 p hg
    simpa only [d1330, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10006 (p : Pattern) (guard : d4148 p = 1) : d1331 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1331, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10005 p hg
    simpa only [d1331, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1331, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d1331, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10007 (p : Pattern) (guard : d4148 p = 1) : d1332 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1332, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d1332, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1332, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1332, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10008 (p : Pattern) (guard : d4148 p = 1) : d1333 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1333, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10007 p hg
    simpa only [d1333, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1333, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9973 p hg
    simpa only [d1333, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10009 (p : Pattern) (guard : d4148 p = 1) : d1334 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1334, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10008 p hg
    simpa only [d1334, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1334, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9975 p hg
    simpa only [d1334, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10010 (p : Pattern) (guard : d4148 p = 1) : d1335 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1335, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10006 p hg
    simpa only [d1335, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1335, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10009 p hg
    simpa only [d1335, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10011 (p : Pattern) (guard : d4148 p = 1) : d1336 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1336, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10004 p hg
    simpa only [d1336, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1336, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10010 p hg
    simpa only [d1336, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10012 (p : Pattern) (guard : d4148 p = 1) : d1338 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1338, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9503 p hg
    simpa only [d1338, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1338, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9962 p hg
    simpa only [d1338, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10013 (p : Pattern) (guard : d4148 p = 1) : d1339 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1339, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10012 p hg
    simpa only [d1339, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1339, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d1339, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10014 (p : Pattern) (guard : d4148 p = 1) : d1340 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1340, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10013 p hg
    simpa only [d1340, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1340, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10009 p hg
    simpa only [d1340, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10015 (p : Pattern) (guard : d4148 p = 1) : d1341 p ≤ (0 : Int) + d1464 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1341, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10014 p hg
    simpa only [d1341, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1341, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1341, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10016 (p : Pattern) (guard : d4148 p = 1) : d1342 p ≤ (0 : Int) + d1465 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1342, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10011 p hg
    simpa only [d1342, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1342, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10015 p hg
    simpa only [d1342, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10017 (p : Pattern) (guard : d4148 p = 1) : d1343 p ≤ (0 : Int) + d1466 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1343, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9989 p hg
    simpa only [d1343, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1343, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10016 p hg
    simpa only [d1343, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10018 (p : Pattern) (guard : d4148 p = 1) : d1344 p ≤ (0 : Int) + d1467 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1344, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9890 p hg
    simpa only [d1344, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1344, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10017 p hg
    simpa only [d1344, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10019 (p : Pattern) (guard : d4148 p = 1) : d1345 p ≤ (0 : Int) + d1468 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1345, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9932 p hg
    simpa only [d1345, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1345, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10018 p hg
    simpa only [d1345, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10020 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (0 : Int) + d1469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9836 p hg
    simpa only [d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10021 (p : Pattern) (guard : d4148 p = 1) : d1346 p ≤ (0 : Int) + d1470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1346, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10020 p hg
    simpa only [d1346, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1346, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9839 p hg
    simpa only [d1346, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10022 (p : Pattern) (guard : d4148 p = 1) : d1347 p ≤ (0 : Int) + d20 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9340 p hg
    simpa only [d4148, d1347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10023 (p : Pattern) (guard : d4148 p = 1) : d1348 p ≤ (0 : Int) + d1100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10022 p hg
    simpa only [d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1348, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10024 (p : Pattern) (guard : d4148 p = 1) : d1349 p ≤ (0 : Int) + d1101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10023 p hg
    simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1349, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10025 (p : Pattern) (guard : d4148 p = 1) : d1350 p ≤ (0 : Int) + d1471 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1350, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10021 p hg
    simpa only [d1350, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1350, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10024 p hg
    simpa only [d1350, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10026 (p : Pattern) (guard : d4148 p = 1) : d1351 p ≤ (0 : Int) + d1472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1351, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9926 p hg
    simpa only [d1351, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1351, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10025 p hg
    simpa only [d1351, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10027 (p : Pattern) (guard : d4148 p = 1) : d1352 p ≤ (0 : Int) + d1473 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1352, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9924 p hg
    simpa only [d1352, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1352, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10026 p hg
    simpa only [d1352, d1473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10028 (p : Pattern) (guard : d4148 p = 1) : d1353 p ≤ (0 : Int) + d1472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1353, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9879 p hg
    simpa only [d1353, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1353, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10025 p hg
    simpa only [d1353, d1472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10029 (p : Pattern) (guard : d4148 p = 1) : d1354 p ≤ (0 : Int) + d1474 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1354, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10028 p hg
    simpa only [d1354, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1354, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1354, d1474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10030 (p : Pattern) (guard : d4148 p = 1) : d1355 p ≤ (0 : Int) + d1475 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1355, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10027 p hg
    simpa only [d1355, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1355, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10029 p hg
    simpa only [d1355, d1475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10031 (p : Pattern) (guard : d4148 p = 1) : d1356 p ≤ (0 : Int) + d1476 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1356, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9917 p hg
    simpa only [d1356, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1356, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10030 p hg
    simpa only [d1356, d1476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10032 (p : Pattern) (guard : d4148 p = 1) : d1357 p ≤ (0 : Int) + d1477 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1357, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9890 p hg
    simpa only [d1357, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1357, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10031 p hg
    simpa only [d1357, d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10033 (p : Pattern) (guard : d4148 p = 1) : d1358 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1358, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9943 p hg
    simpa only [d1358, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1358, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1358, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10034 (p : Pattern) (guard : d4148 p = 1) : d1359 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1359, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10033 p hg
    simpa only [d1359, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1359, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10001 p hg
    simpa only [d1359, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10035 (p : Pattern) (guard : d4148 p = 1) : d1360 p ≤ (0 : Int) + d1461 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1360, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10034 p hg
    simpa only [d1360, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1360, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9957 p hg
    simpa only [d1360, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10036 (p : Pattern) (guard : d4148 p = 1) : d1361 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1361, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9941 p hg
    simpa only [d1361, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1361, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10035 p hg
    simpa only [d1361, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10037 (p : Pattern) (guard : d4148 p = 1) : d1362 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1362, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9967 p hg
    simpa only [d1362, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1362, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10009 p hg
    simpa only [d1362, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10038 (p : Pattern) (guard : d4148 p = 1) : d1363 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1363, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10036 p hg
    simpa only [d1363, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1363, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10037 p hg
    simpa only [d1363, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10039 (p : Pattern) (guard : d4148 p = 1) : d1364 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1364, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9980 p hg
    simpa only [d1364, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1364, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10009 p hg
    simpa only [d1364, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10040 (p : Pattern) (guard : d4148 p = 1) : d1365 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1365, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10039 p hg
    simpa only [d1365, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1365, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9987 p hg
    simpa only [d1365, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10041 (p : Pattern) (guard : d4148 p = 1) : d1366 p ≤ (0 : Int) + d1478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1366, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10038 p hg
    simpa only [d1366, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1366, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10040 p hg
    simpa only [d1366, d1478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10042 (p : Pattern) (guard : d4148 p = 1) : d1298 p ≤ (0 : Int) + d1479 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1298, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9543 p hg
    simpa only [d1298, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1298, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1298, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10043 (p : Pattern) (guard : d4148 p = 1) : d1368 p ≤ (0 : Int) + d1480 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1368, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9531 p hg
    simpa only [d1368, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1368, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10042 p hg
    simpa only [d1368, d1480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10044 (p : Pattern) (guard : d4148 p = 1) : d1369 p ≤ (0 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9542 p hg
    simpa only [d4148, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10045 (p : Pattern) (guard : d4148 p = 1) : d1371 p ≤ (0 : Int) + d1481 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1371, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10044 p hg
    simpa only [d1371, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1371, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9535 p hg
    simpa only [d1371, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10046 (p : Pattern) (guard : d4148 p = 1) : d1373 p ≤ (0 : Int) + d1482 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1373, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10045 p hg
    simpa only [d1373, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1373, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9537 p hg
    simpa only [d1373, d1482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10047 (p : Pattern) (guard : d4148 p = 1) : d1374 p ≤ (0 : Int) + d1483 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1374, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10043 p hg
    simpa only [d1374, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1374, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10046 p hg
    simpa only [d1374, d1483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10048 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10049 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (0 : Int) + d925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d1289, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10048 p hg
    simpa only [d4148, d1289, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10050 (p : Pattern) (guard : d4148 p = 1) : d1300 p ≤ (0 : Int) + d1124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10049 p hg
    simpa only [d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1300, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10051 (p : Pattern) (guard : d4148 p = 1) : d1333 p ≤ (0 : Int) + d1484 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1333, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10007 p hg
    simpa only [d1333, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1333, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10050 p hg
    simpa only [d1333, d1484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10052 (p : Pattern) (guard : d4148 p = 1) : d1375 p ≤ (0 : Int) + d1375 p := by
  omega
theorem compare10053 (p : Pattern) (guard : d4148 p = 1) : d1376 p ≤ (0 : Int) + d1485 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1376, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10049 p hg
    simpa only [d1376, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1376, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10052 p hg
    simpa only [d1376, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10054 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1127 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10055 (p : Pattern) (guard : d4148 p = 1) : d1375 p ≤ (0 : Int) + d1128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1375, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8334 p hg
    simpa only [d4148, d1375, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1375, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10054 p hg
    simpa only [d4148, d1375, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10056 (p : Pattern) (guard : d4148 p = 1) : d1377 p ≤ (0 : Int) + d1129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10055 p hg
    simpa only [d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1377, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10057 (p : Pattern) (guard : d4148 p = 1) : d1378 p ≤ (0 : Int) + d1486 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1378, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10053 p hg
    simpa only [d1378, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1378, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10056 p hg
    simpa only [d1378, d1486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10058 (p : Pattern) (guard : d4148 p = 1) : d1379 p ≤ (0 : Int) + d1487 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1379, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10051 p hg
    simpa only [d1379, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1379, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10057 p hg
    simpa only [d1379, d1487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10059 (p : Pattern) (guard : d4148 p = 1) : d1380 p ≤ (0 : Int) + d1488 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1380, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10047 p hg
    simpa only [d1380, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1380, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10058 p hg
    simpa only [d1380, d1488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10060 (p : Pattern) (guard : d4148 p = 1) : d1381 p ≤ (0 : Int) + d1489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1381, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1381, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1381, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1381, d1489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10061 (p : Pattern) (guard : d4148 p = 1) : d1369 p ≤ (0 : Int) + d1133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1369, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d1369, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1369, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9960 p hg
    simpa only [d4148, d1369, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10062 (p : Pattern) (guard : d4148 p = 1) : d1382 p ≤ (0 : Int) + d1490 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1382, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10061 p hg
    simpa only [d1382, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1382, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d1382, d1490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10063 (p : Pattern) (guard : d4148 p = 1) : d1383 p ≤ (0 : Int) + d1491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1383, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10060 p hg
    simpa only [d1383, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1383, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10062 p hg
    simpa only [d1383, d1491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10064 (p : Pattern) (guard : d4148 p = 1) : d1384 p ≤ (0 : Int) + d1492 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1384, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10063 p hg
    simpa only [d1384, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1384, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d1384, d1492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10065 (p : Pattern) (guard : d4148 p = 1) : d1385 p ≤ (0 : Int) + d1385 p := by
  omega
theorem compare10066 (p : Pattern) (guard : d4148 p = 1) : d1386 p ≤ (0 : Int) + d1493 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1386, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d1386, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1386, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10065 p hg
    simpa only [d1386, d1493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10067 (p : Pattern) (guard : d4148 p = 1) : d1385 p ≤ (0 : Int) + d1137 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1385, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8348 p hg
    simpa only [d4148, d1385, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1385, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d4148, d1385, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10068 (p : Pattern) (guard : d4148 p = 1) : d1387 p ≤ (0 : Int) + d1138 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10067 p hg
    simpa only [d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1387, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10069 (p : Pattern) (guard : d4148 p = 1) : d1388 p ≤ (0 : Int) + d1494 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1388, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10066 p hg
    simpa only [d1388, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1388, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10068 p hg
    simpa only [d1388, d1494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10070 (p : Pattern) (guard : d4148 p = 1) : d1389 p ≤ (0 : Int) + d1141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2413 p hg
    simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1389, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10071 (p : Pattern) (guard : d4148 p = 1) : d1390 p ≤ (0 : Int) + d1495 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1390, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10069 p hg
    simpa only [d1390, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1390, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10070 p hg
    simpa only [d1390, d1495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10072 (p : Pattern) (guard : d4148 p = 1) : d1391 p ≤ (0 : Int) + d1496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1391, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10064 p hg
    simpa only [d1391, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1391, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10071 p hg
    simpa only [d1391, d1496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10073 (p : Pattern) (guard : d4148 p = 1) : d1392 p ≤ (0 : Int) + d1497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1392, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10059 p hg
    simpa only [d1392, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1392, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10072 p hg
    simpa only [d1392, d1497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10074 (p : Pattern) (guard : d4148 p = 1) : d1393 p ≤ (0 : Int) + d1498 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1393, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10072 p hg
    simpa only [d1393, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1393, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1393, d1498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10075 (p : Pattern) (guard : d4148 p = 1) : d1394 p ≤ (0 : Int) + d1499 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1394, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10073 p hg
    simpa only [d1394, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1394, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10074 p hg
    simpa only [d1394, d1499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10076 (p : Pattern) (guard : d4148 p = 1) : d1395 p ≤ (0 : Int) + d1500 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1395, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10041 p hg
    simpa only [d1395, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1395, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10075 p hg
    simpa only [d1395, d1500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10077 (p : Pattern) (guard : d4148 p = 1) : d1396 p ≤ (0 : Int) + d1501 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1396, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9890 p hg
    simpa only [d1396, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1396, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10076 p hg
    simpa only [d1396, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10078 (p : Pattern) (guard : d4148 p = 1) : d1397 p ≤ (0 : Int) + d1502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1397, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10032 p hg
    simpa only [d1397, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1397, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10077 p hg
    simpa only [d1397, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10079 (p : Pattern) (guard : d4148 p = 1) : d1398 p ≤ (0 : Int) + d1503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1398, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10019 p hg
    simpa only [d1398, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1398, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10078 p hg
    simpa only [d1398, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
