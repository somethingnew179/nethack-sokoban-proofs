/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1260 (p : Pattern) (guard : d770 p = 1) : d122 p ≤ (0 : Int) + d384 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d122, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d122, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d122, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1259 p hg
    simpa only [d122, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1261 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (0 : Int) + d385 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d179, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d179, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d179, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d179, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1262 (p : Pattern) (guard : d0 p = 1) : d278 p ≤ (0 : Int) + d391 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1263 (p : Pattern) (guard : d984 p = 1) : d279 p ≤ (0 : Int) + d392 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d279, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1261 p hg
    simpa only [d984, d279, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d279, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1262 p hg
    simpa only [d984, d279, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1264 (p : Pattern) (guard : d984 p = 1) : d280 p ≤ (0 : Int) + d393 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d280, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d280, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d280, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1263 p hg
    simpa only [d280, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1265 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (0 : Int) + d394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d68, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d68, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d68, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d68, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1266 (p : Pattern) (guard : d0 p = 1) : d281 p ≤ (0 : Int) + d395 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1267 (p : Pattern) (guard : d984 p = 1) : d282 p ≤ (0 : Int) + d396 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d282, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d984, d282, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d282, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1266 p hg
    simpa only [d984, d282, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1268 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (0 : Int) + d397 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d181, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d181, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d181, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d181, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1269 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1270 (p : Pattern) (guard : d984 p = 1) : d284 p ≤ (0 : Int) + d399 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d284, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1268 p hg
    simpa only [d984, d284, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d284, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1269 p hg
    simpa only [d984, d284, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1271 (p : Pattern) (guard : d984 p = 1) : d285 p ≤ (0 : Int) + d400 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d285, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d285, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d285, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1270 p hg
    simpa only [d285, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1272 (p : Pattern) (guard : d984 p = 1) : d286 p ≤ (0 : Int) + d401 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d286, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1264 p hg
    simpa only [d286, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d286, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d286, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1273 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1274 (p : Pattern) (guard : d984 p = 1) : d287 p ≤ (0 : Int) + d402 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d287, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d984, d287, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d287, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1273 p hg
    simpa only [d984, d287, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1275 (p : Pattern) (guard : d984 p = 1) : d288 p ≤ (0 : Int) + d403 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d288, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d288, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d288, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d288, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1276 (p : Pattern) (guard : d984 p = 1) : d289 p ≤ (0 : Int) + d404 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d289, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1272 p hg
    simpa only [d289, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d289, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d289, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1277 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (0 : Int) + d137 p := by
  omega
theorem compare1278 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d290 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1279 (p : Pattern) (guard : d770 p = 1) : d137 p ≤ (0 : Int) + d405 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1280 (p : Pattern) (guard : d770 p = 1) : d139 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d139, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d139, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d139, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1279 p hg
    simpa only [d139, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1281 (p : Pattern) (guard : d770 p = 1) : d153 p ≤ (0 : Int) + d407 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d153, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d153, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d153, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d153, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1282 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (0 : Int) + d408 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d186, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d186, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d186, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1281 p hg
    simpa only [d186, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1283 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1284 (p : Pattern) (guard : d984 p = 1) : d296 p ≤ (0 : Int) + d413 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d296, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d984, d296, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d296, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d984, d296, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1285 (p : Pattern) (guard : d984 p = 1) : d297 p ≤ (0 : Int) + d414 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d297, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1284 p hg
    simpa only [d297, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d297, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d297, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1286 (p : Pattern) (guard : d770 p = 1) : d138 p ≤ (0 : Int) + d415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d138, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d138, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d138, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1279 p hg
    simpa only [d138, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1287 (p : Pattern) (guard : d770 p = 1) : d140 p ≤ (0 : Int) + d416 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d140, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1286 p hg
    simpa only [d140, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d140, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d140, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1288 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (0 : Int) + d417 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d188, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1287 p hg
    simpa only [d188, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d188, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d188, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1289 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1290 (p : Pattern) (guard : d984 p = 1) : d301 p ≤ (0 : Int) + d421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d301, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1288 p hg
    simpa only [d984, d301, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d301, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d984, d301, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1291 (p : Pattern) (guard : d984 p = 1) : d302 p ≤ (0 : Int) + d422 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d302, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1290 p hg
    simpa only [d302, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d302, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d302, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1292 (p : Pattern) (guard : d984 p = 1) : d303 p ≤ (0 : Int) + d423 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d303, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1285 p hg
    simpa only [d303, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d303, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d303, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1293 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (0 : Int) + d424 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d191, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1281 p hg
    simpa only [d191, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d191, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d191, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1294 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d425 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1295 (p : Pattern) (guard : d984 p = 1) : d305 p ≤ (0 : Int) + d426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d305, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1293 p hg
    simpa only [d984, d305, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d305, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1294 p hg
    simpa only [d984, d305, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1296 (p : Pattern) (guard : d984 p = 1) : d306 p ≤ (0 : Int) + d427 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d306, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1295 p hg
    simpa only [d306, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d306, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d306, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1297 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d428 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d307, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1296 p hg
    simpa only [d307, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d307, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d307, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1298 (p : Pattern) (guard : d984 p = 1) : d308 p ≤ (0 : Int) + d429 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d308, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d308, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d308, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1297 p hg
    simpa only [d308, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1299 (p : Pattern) (guard : d984 p = 1) : d309 p ≤ (0 : Int) + d430 p := by
  cases selected : p 108 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d309, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1276 p hg
    simpa only [d309, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d309, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1298 p hg
    simpa only [d309, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1300 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1301 (p : Pattern) (guard : d770 p = 1) : d7 p ≤ (0 : Int) + d22 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1302 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d265 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1303 (p : Pattern) (guard : d770 p = 1) : d56 p ≤ (0 : Int) + d377 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1304 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (0 : Int) + d378 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d57, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1301 p hg
    simpa only [d57, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d57, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1303 p hg
    simpa only [d57, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1305 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (0 : Int) + d379 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1306 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1307 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (0 : Int) + d386 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1306 p hg
    simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1308 (p : Pattern) (guard : d770 p = 1) : d106 p ≤ (0 : Int) + d387 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d106, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1301 p hg
    simpa only [d106, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d106, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d106, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1309 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d274 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1310 (p : Pattern) (guard : d770 p = 1) : d120 p ≤ (0 : Int) + d388 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1309 p hg
    simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1311 (p : Pattern) (guard : d770 p = 1) : d121 p ≤ (0 : Int) + d389 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d121, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d121, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d121, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d121, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1312 (p : Pattern) (guard : d770 p = 1) : d122 p ≤ (0 : Int) + d390 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d122, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1308 p hg
    simpa only [d122, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d122, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d122, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1313 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (0 : Int) + d391 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d179, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1308 p hg
    simpa only [d179, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d179, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1312 p hg
    simpa only [d179, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1314 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (0 : Int) + d392 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1261 p hg
    simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1313 p hg
    simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1315 (p : Pattern) (guard : d770 p = 1) : d180 p ≤ (0 : Int) + d393 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d180, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1305 p hg
    simpa only [d180, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d180, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1314 p hg
    simpa only [d180, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1316 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (0 : Int) + d395 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d68, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d68, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d68, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d68, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1317 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (0 : Int) + d396 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1316 p hg
    simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1318 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (0 : Int) + d398 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d181, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1312 p hg
    simpa only [d181, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d181, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d181, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1319 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (0 : Int) + d399 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1268 p hg
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1318 p hg
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1320 (p : Pattern) (guard : d770 p = 1) : d182 p ≤ (0 : Int) + d400 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d182, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1317 p hg
    simpa only [d182, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d182, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d182, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1321 (p : Pattern) (guard : d770 p = 1) : d183 p ≤ (0 : Int) + d401 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d183, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1315 p hg
    simpa only [d183, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d183, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1320 p hg
    simpa only [d183, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1322 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (0 : Int) + d402 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1323 (p : Pattern) (guard : d770 p = 1) : d184 p ≤ (0 : Int) + d403 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d184, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1320 p hg
    simpa only [d184, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d184, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d184, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1324 (p : Pattern) (guard : d770 p = 1) : d185 p ≤ (0 : Int) + d404 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d185, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d185, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d185, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d185, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1325 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d291 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1326 (p : Pattern) (guard : d770 p = 1) : d137 p ≤ (0 : Int) + d409 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1325 p hg
    simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1327 (p : Pattern) (guard : d770 p = 1) : d139 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d139, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d139, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d139, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1326 p hg
    simpa only [d139, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1328 (p : Pattern) (guard : d770 p = 1) : d153 p ≤ (0 : Int) + d411 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d153, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d153, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d153, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1327 p hg
    simpa only [d153, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1329 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (0 : Int) + d412 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d186, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d186, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d186, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d186, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1330 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (0 : Int) + d413 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1329 p hg
    simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1331 (p : Pattern) (guard : d770 p = 1) : d187 p ≤ (0 : Int) + d414 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d187, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1330 p hg
    simpa only [d187, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d187, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d187, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1332 (p : Pattern) (guard : d770 p = 1) : d138 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d138, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1301 p hg
    simpa only [d138, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d138, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1326 p hg
    simpa only [d138, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1333 (p : Pattern) (guard : d770 p = 1) : d140 p ≤ (0 : Int) + d419 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d140, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1332 p hg
    simpa only [d140, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d140, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1327 p hg
    simpa only [d140, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1334 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (0 : Int) + d420 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d188, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1333 p hg
    simpa only [d188, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d188, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d188, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1335 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (0 : Int) + d421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1288 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1334 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1336 (p : Pattern) (guard : d770 p = 1) : d189 p ≤ (0 : Int) + d422 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d189, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1335 p hg
    simpa only [d189, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d189, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d189, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1337 (p : Pattern) (guard : d770 p = 1) : d190 p ≤ (0 : Int) + d423 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d190, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1331 p hg
    simpa only [d190, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d190, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1336 p hg
    simpa only [d190, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1338 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (0 : Int) + d425 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d191, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d191, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d191, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d191, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1339 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (0 : Int) + d426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1293 p hg
    simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1338 p hg
    simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1340 (p : Pattern) (guard : d770 p = 1) : d192 p ≤ (0 : Int) + d427 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d192, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1339 p hg
    simpa only [d192, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d192, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d192, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1341 (p : Pattern) (guard : d770 p = 1) : d193 p ≤ (0 : Int) + d428 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d193, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1340 p hg
    simpa only [d193, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d193, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d193, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1342 (p : Pattern) (guard : d770 p = 1) : d194 p ≤ (0 : Int) + d429 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d194, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1337 p hg
    simpa only [d194, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d194, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1341 p hg
    simpa only [d194, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1343 (p : Pattern) (guard : d770 p = 1) : d195 p ≤ (0 : Int) + d430 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d195, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1324 p hg
    simpa only [d195, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d195, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1342 p hg
    simpa only [d195, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1344 (p : Pattern) (guard : d769 p = 1) : d195 p ≤ (1 : Int) + d195 p := by
  omega
theorem compare1345 (p : Pattern) (guard : d767 p = 1) : d195 p ≤ (1 : Int) + d195 p := by
  omega
theorem compare1346 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1347 (p : Pattern) (guard : d770 p = 1) : d7 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1348 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1349 (p : Pattern) (guard : d770 p = 1) : d56 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1348 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1350 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d57, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d57, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d57, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1349 p hg
    simpa only [d57, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1351 (p : Pattern) (guard : d986 p = 1) : d57 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1352 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1353 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1352 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1354 (p : Pattern) (guard : d770 p = 1) : d106 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d106, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d106, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d106, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d106, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1355 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1356 (p : Pattern) (guard : d770 p = 1) : d120 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1355 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1357 (p : Pattern) (guard : d770 p = 1) : d121 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d121, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1356 p hg
    simpa only [d121, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d121, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d121, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1358 (p : Pattern) (guard : d770 p = 1) : d122 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d122, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1354 p hg
    simpa only [d122, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d122, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1357 p hg
    simpa only [d122, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1359 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d179, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1354 p hg
    simpa only [d179, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d179, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1358 p hg
    simpa only [d179, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1360 (p : Pattern) (guard : d986 p = 1) : d179 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1359 p hg
    simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1361 (p : Pattern) (guard : d986 p = 1) : d180 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1351 p hg
    simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1360 p hg
    simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1362 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d68, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d68, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d68, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d68, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1363 (p : Pattern) (guard : d986 p = 1) : d68 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1362 p hg
    simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1364 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d181, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1358 p hg
    simpa only [d181, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d181, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d181, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1365 (p : Pattern) (guard : d986 p = 1) : d181 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1366 (p : Pattern) (guard : d986 p = 1) : d182 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1363 p hg
    simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1367 (p : Pattern) (guard : d986 p = 1) : d183 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1361 p hg
    simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1366 p hg
    simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1368 (p : Pattern) (guard : d986 p = 1) : d55 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1369 (p : Pattern) (guard : d986 p = 1) : d184 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1366 p hg
    simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1370 (p : Pattern) (guard : d986 p = 1) : d185 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1367 p hg
    simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1369 p hg
    simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1371 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d143 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1372 (p : Pattern) (guard : d770 p = 1) : d137 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1371 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1373 (p : Pattern) (guard : d770 p = 1) : d139 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d139, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1356 p hg
    simpa only [d139, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d139, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1372 p hg
    simpa only [d139, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1374 (p : Pattern) (guard : d770 p = 1) : d153 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d153, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d153, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d153, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d153, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1375 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d186, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d186, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d186, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1374 p hg
    simpa only [d186, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1376 (p : Pattern) (guard : d986 p = 1) : d186 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1375 p hg
    simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1377 (p : Pattern) (guard : d986 p = 1) : d187 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1376 p hg
    simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1378 (p : Pattern) (guard : d770 p = 1) : d138 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1372 p hg
    simpa only [d138, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1379 (p : Pattern) (guard : d770 p = 1) : d140 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d140, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1378 p hg
    simpa only [d140, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d140, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d140, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1380 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d188, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1379 p hg
    simpa only [d188, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d188, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d188, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1381 (p : Pattern) (guard : d986 p = 1) : d188 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1380 p hg
    simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1382 (p : Pattern) (guard : d986 p = 1) : d189 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1381 p hg
    simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1383 (p : Pattern) (guard : d986 p = 1) : d190 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1377 p hg
    simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1382 p hg
    simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1384 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d191, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1374 p hg
    simpa only [d191, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d191, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d191, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1385 (p : Pattern) (guard : d986 p = 1) : d191 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1384 p hg
    simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1386 (p : Pattern) (guard : d986 p = 1) : d192 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1385 p hg
    simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1387 (p : Pattern) (guard : d986 p = 1) : d193 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1386 p hg
    simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1388 (p : Pattern) (guard : d986 p = 1) : d194 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1383 p hg
    simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1387 p hg
    simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1389 (p : Pattern) (guard : d986 p = 1) : d195 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1370 p hg
    simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1388 p hg
    simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1390 (p : Pattern) (guard : d768 p = 1) : d195 p ≤ (1 : Int) + d195 p := by
  omega
theorem compare1391 (p : Pattern) (guard : d987 p = 1) : d64 p ≤ (0 : Int) + d64 p := by
  omega
theorem compare1392 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1393 (p : Pattern) (guard : d794 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d794, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1394 (p : Pattern) (guard : d987 p = 1) : d108 p ≤ (0 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1392 p hg
    simpa only [d987, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d987, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1395 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1396 (p : Pattern) (guard : d794 p = 1) : d110 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare696 p hg
    simpa only [d794, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1397 (p : Pattern) (guard : d987 p = 1) : d111 p ≤ (0 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1395 p hg
    simpa only [d987, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d987, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1398 (p : Pattern) (guard : d987 p = 1) : d112 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1394 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1397 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1399 (p : Pattern) (guard : d987 p = 1) : d113 p ≤ (0 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1391 p hg
    simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1398 p hg
    simpa only [d113, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
