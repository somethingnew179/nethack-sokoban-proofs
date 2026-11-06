/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1260 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1259 p hg
    simpa only [d107, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1261 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d108, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d108, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1262 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d109, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1261 p hg
    simpa only [d109, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1263 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1257 p hg
    simpa only [d110, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1262 p hg
    simpa only [d110, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1264 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d111, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1263 p hg
    simpa only [d111, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1265 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d11 p := by
  change (5 : Int) ≤ (0 : Int) + 11
  decide
theorem compare1266 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1267 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1266 p hg
    simpa only [d107, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1268 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d108, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1269 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1268 p hg
    simpa only [d109, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1270 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1257 p hg
    simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1269 p hg
    simpa only [d110, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1271 (p : Pattern) (guard : d1 p = 1) : d112 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1272 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1270 p hg
    simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d113, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1273 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1264 p hg
    simpa only [d114, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1272 p hg
    simpa only [d114, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1274 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d103 p := by
  omega
theorem compare1275 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d7 p := by
  change (3 : Int) ≤ (0 : Int) + 7
  decide
theorem compare1276 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1277 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1276 p hg
    simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1278 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d117, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1279 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d118, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d118, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1280 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d12 p := by
  change (7 : Int) ≤ (0 : Int) + 12
  decide
theorem compare1281 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1282 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1281 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1283 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1284 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d122, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d122, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1285 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1279 p hg
    simpa only [d123, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1284 p hg
    simpa only [d123, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1286 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d124, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1287 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d125, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d125, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1288 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1286 p hg
    simpa only [d126, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1287 p hg
    simpa only [d126, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1289 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1285 p hg
    simpa only [d127, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1288 p hg
    simpa only [d127, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1290 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1267 p hg
    simpa only [d125, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d125, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1291 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1286 p hg
    simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1290 p hg
    simpa only [d126, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1292 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1293 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1291 p hg
    simpa only [d129, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d129, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1294 (p : Pattern) (guard : d1 p = 1) : d130 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1289 p hg
    simpa only [d130, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1293 p hg
    simpa only [d130, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1295 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d131, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1273 p hg
    simpa only [d131, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d131, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1294 p hg
    simpa only [d131, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1296 (p : Pattern) (guard : d0 p = 1) : d146 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1297 (p : Pattern) (guard : d4077 p = 1) : d147 p ≤ (0 : Int) + d146 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1295 p hg
    simpa only [d4077, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1296 p hg
    simpa only [d4077, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1298 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d132, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1299 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1300 (p : Pattern) (guard : d1 p = 1) : d149 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1298 p hg
    simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1299 p hg
    simpa only [d149, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1301 (p : Pattern) (guard : d1 p = 1) : d150 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1300 p hg
    simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d150, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1302 (p : Pattern) (guard : d1 p = 1) : d151 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1301 p hg
    simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d151, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1303 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1273 p hg
    simpa only [d152, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d152, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1304 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1305 (p : Pattern) (guard : d4077 p = 1) : d157 p ≤ (0 : Int) + d156 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1303 p hg
    simpa only [d4077, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1304 p hg
    simpa only [d4077, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1306 (p : Pattern) (guard : d4077 p = 1) : d158 p ≤ (0 : Int) + d4084 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d158, d4084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1297 p hg
    simpa only [d158, d4084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d158, d4084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1305 p hg
    simpa only [d158, d4084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1307 (p : Pattern) (guard : d1 p = 1) : d159 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1308 (p : Pattern) (guard : d1 p = 1) : d160 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1307 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1309 (p : Pattern) (guard : d1 p = 1) : d161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1308 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1310 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1311 (p : Pattern) (guard : d4077 p = 1) : d162 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1309 p hg
    simpa only [d4077, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4077, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1312 (p : Pattern) (guard : d4077 p = 1) : d163 p ≤ (0 : Int) + d4085 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d163, d4085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1305 p hg
    simpa only [d163, d4085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d163, d4085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d163, d4085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1313 (p : Pattern) (guard : d4077 p = 1) : d164 p ≤ (0 : Int) + d4086 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d164, d4086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1306 p hg
    simpa only [d164, d4086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d164, d4086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1312 p hg
    simpa only [d164, d4086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1314 (p : Pattern) (guard : d4077 p = 1) : d165 p ≤ (0 : Int) + d4085 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d165, d4085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1305 p hg
    simpa only [d165, d4085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d165, d4085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d165, d4085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1315 (p : Pattern) (guard : d4077 p = 1) : d166 p ≤ (0 : Int) + d4086 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d166, d4086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1306 p hg
    simpa only [d166, d4086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d166, d4086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1314 p hg
    simpa only [d166, d4086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1316 (p : Pattern) (guard : d4077 p = 1) : d167 p ≤ (0 : Int) + d4086 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1313 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1315 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1317 (p : Pattern) (guard : d4077 p = 1) : d168 p ≤ (0 : Int) + d4087 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d168, d4087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1245 p hg
    simpa only [d168, d4087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d168, d4087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1316 p hg
    simpa only [d168, d4087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1318 (p : Pattern) (guard : d4077 p = 1) : d169 p ≤ (0 : Int) + d4088 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d169, d4088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1245 p hg
    simpa only [d169, d4088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d169, d4088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1317 p hg
    simpa only [d169, d4088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1319 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d12 p := by
  change (5 : Int) ≤ (0 : Int) + 12
  decide
theorem compare1320 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1321 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1320 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1322 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1323 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1324 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1257 p hg
    simpa only [d110, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d110, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1325 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d111, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1324 p hg
    simpa only [d111, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1326 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1324 p hg
    simpa only [d113, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d113, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1327 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1325 p hg
    simpa only [d114, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1326 p hg
    simpa only [d114, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1328 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1329 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1286 p hg
    simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1328 p hg
    simpa only [d126, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1330 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1285 p hg
    simpa only [d127, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1329 p hg
    simpa only [d127, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1331 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1329 p hg
    simpa only [d129, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1292 p hg
    simpa only [d129, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1332 (p : Pattern) (guard : d1 p = 1) : d130 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d130, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1330 p hg
    simpa only [d130, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d130, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1331 p hg
    simpa only [d130, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1333 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d131, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1327 p hg
    simpa only [d131, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d131, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1332 p hg
    simpa only [d131, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1334 (p : Pattern) (guard : d0 p = 1) : d219 p ≤ (0 : Int) + d219 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1335 (p : Pattern) (guard : d4077 p = 1) : d220 p ≤ (0 : Int) + d219 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1333 p hg
    simpa only [d4077, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1334 p hg
    simpa only [d4077, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1336 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d152, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1327 p hg
    simpa only [d152, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d152, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d152, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1337 (p : Pattern) (guard : d0 p = 1) : d221 p ≤ (0 : Int) + d221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1338 (p : Pattern) (guard : d4077 p = 1) : d222 p ≤ (0 : Int) + d221 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1336 p hg
    simpa only [d4077, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1337 p hg
    simpa only [d4077, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1339 (p : Pattern) (guard : d4077 p = 1) : d223 p ≤ (0 : Int) + d4089 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d223, d4089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1335 p hg
    simpa only [d223, d4089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d223, d4089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1338 p hg
    simpa only [d223, d4089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1340 (p : Pattern) (guard : d4077 p = 1) : d224 p ≤ (0 : Int) + d4090 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d224, d4090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1338 p hg
    simpa only [d224, d4090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d224, d4090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1311 p hg
    simpa only [d224, d4090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1341 (p : Pattern) (guard : d4077 p = 1) : d225 p ≤ (0 : Int) + d4091 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d225, d4091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1339 p hg
    simpa only [d225, d4091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d225, d4091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1340 p hg
    simpa only [d225, d4091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1342 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (0 : Int) + d268 p := by
  omega
theorem compare1343 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (0 : Int) + d270 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1342 p hg
    simpa only [d269, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d269, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1344 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d5 p := by
  change (3 : Int) ≤ (0 : Int) + 5
  decide
theorem compare1345 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1344 p hg
    simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d115, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1346 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1344 p hg
    simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1345 p hg
    simpa only [d116, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1347 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (0 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d268, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d268, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1348 (p : Pattern) (guard : d1 p = 1) : d270 p ≤ (0 : Int) + d283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d270, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d270, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d270, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d270, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1349 (p : Pattern) (guard : d1 p = 1) : d271 p ≤ (0 : Int) + d284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d271, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1343 p hg
    simpa only [d271, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d271, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1348 p hg
    simpa only [d271, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1350 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (0 : Int) + d273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d268, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d268, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1351 (p : Pattern) (guard : d1 p = 1) : d272 p ≤ (0 : Int) + d274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d272, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d272, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d272, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d272, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1352 (p : Pattern) (guard : d1 p = 1) : d273 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1353 (p : Pattern) (guard : d1 p = 1) : d274 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1352 p hg
    simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1354 (p : Pattern) (guard : d1 p = 1) : d275 p ≤ (0 : Int) + d285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1351 p hg
    simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d275, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1355 (p : Pattern) (guard : d1 p = 1) : d276 p ≤ (0 : Int) + d286 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d276, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1349 p hg
    simpa only [d276, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d276, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1354 p hg
    simpa only [d276, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1356 (p : Pattern) (guard : d1 p = 1) : d277 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare850 p hg
    simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1357 (p : Pattern) (guard : d1 p = 1) : d278 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1356 p hg
    simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1358 (p : Pattern) (guard : d1 p = 1) : d279 p ≤ (0 : Int) + d287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d279, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1354 p hg
    simpa only [d279, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d279, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1357 p hg
    simpa only [d279, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1359 (p : Pattern) (guard : d1 p = 1) : d280 p ≤ (0 : Int) + d288 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d280, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1355 p hg
    simpa only [d280, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d280, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1358 p hg
    simpa only [d280, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1360 (p : Pattern) (guard : d1 p = 1) : d281 p ≤ (0 : Int) + d289 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d281, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1327 p hg
    simpa only [d281, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d281, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1359 p hg
    simpa only [d281, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1361 (p : Pattern) (guard : d0 p = 1) : d289 p ≤ (0 : Int) + d289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1362 (p : Pattern) (guard : d4077 p = 1) : d290 p ≤ (0 : Int) + d289 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1360 p hg
    simpa only [d4077, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1361 p hg
    simpa only [d4077, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1363 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1364 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1363 p hg
    simpa only [d105, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d105, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1365 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d117, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1366 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (0 : Int) + d298 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1347 p hg
    simpa only [d269, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1365 p hg
    simpa only [d269, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1367 (p : Pattern) (guard : d1 p = 1) : d291 p ≤ (0 : Int) + d299 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d291, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d291, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d291, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1366 p hg
    simpa only [d291, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1368 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (0 : Int) + d292 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d269, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1278 p hg
    simpa only [d269, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1369 (p : Pattern) (guard : d1 p = 1) : d292 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1352 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1283 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1370 (p : Pattern) (guard : d1 p = 1) : d293 p ≤ (0 : Int) + d300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d293, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1368 p hg
    simpa only [d293, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d293, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1369 p hg
    simpa only [d293, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1371 (p : Pattern) (guard : d1 p = 1) : d294 p ≤ (0 : Int) + d301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d294, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1367 p hg
    simpa only [d294, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d294, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1370 p hg
    simpa only [d294, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1372 (p : Pattern) (guard : d1 p = 1) : d295 p ≤ (0 : Int) + d302 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d295, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1370 p hg
    simpa only [d295, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d295, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1357 p hg
    simpa only [d295, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1373 (p : Pattern) (guard : d1 p = 1) : d296 p ≤ (0 : Int) + d303 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d296, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1371 p hg
    simpa only [d296, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d296, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1372 p hg
    simpa only [d296, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1374 (p : Pattern) (guard : d1 p = 1) : d297 p ≤ (0 : Int) + d304 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d297, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1373 p hg
    simpa only [d297, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d297, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1302 p hg
    simpa only [d297, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1375 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1376 (p : Pattern) (guard : d4077 p = 1) : d305 p ≤ (0 : Int) + d304 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1374 p hg
    simpa only [d4077, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1375 p hg
    simpa only [d4077, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1377 (p : Pattern) (guard : d4077 p = 1) : d306 p ≤ (0 : Int) + d4092 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d306, d4092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1362 p hg
    simpa only [d306, d4092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d306, d4092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1376 p hg
    simpa only [d306, d4092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1378 (p : Pattern) (guard : d4077 p = 1) : d307 p ≤ (0 : Int) + d4093 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d307, d4093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1376 p hg
    simpa only [d307, d4093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d307, d4093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d307, d4093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1379 (p : Pattern) (guard : d4077 p = 1) : d308 p ≤ (0 : Int) + d4094 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d308, d4094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1377 p hg
    simpa only [d308, d4094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d308, d4094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1378 p hg
    simpa only [d308, d4094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1380 (p : Pattern) (guard : d4077 p = 1) : d309 p ≤ (0 : Int) + d4095 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d309, d4095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1341 p hg
    simpa only [d309, d4095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d309, d4095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1379 p hg
    simpa only [d309, d4095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1381 (p : Pattern) (guard : d4077 p = 1) : d310 p ≤ (0 : Int) + d4096 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d310, d4096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1245 p hg
    simpa only [d310, d4096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d310, d4096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1380 p hg
    simpa only [d310, d4096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1382 (p : Pattern) (guard : d4077 p = 1) : d311 p ≤ (0 : Int) + d4097 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d311, d4097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1245 p hg
    simpa only [d311, d4097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d311, d4097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1381 p hg
    simpa only [d311, d4097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1383 (p : Pattern) (guard : d4077 p = 1) : d312 p ≤ (0 : Int) + d4098 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d312, d4098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1318 p hg
    simpa only [d312, d4098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d312, d4098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1382 p hg
    simpa only [d312, d4098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1384 (p : Pattern) (guard : d1 p = 1) : d162 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1309 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1385 (p : Pattern) (guard : d1 p = 1) : d163 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d163, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1167 p hg
    simpa only [d163, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d163, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1384 p hg
    simpa only [d163, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1386 (p : Pattern) (guard : d1 p = 1) : d164 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d164, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d164, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d164, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1385 p hg
    simpa only [d164, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1387 (p : Pattern) (guard : d0 p = 1) : d166 p ≤ (0 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1388 (p : Pattern) (guard : d4058 p = 1) : d167 p ≤ (0 : Int) + d166 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1386 p hg
    simpa only [d4058, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1387 p hg
    simpa only [d4058, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1389 (p : Pattern) (guard : d4058 p = 1) : d168 p ≤ (0 : Int) + d4060 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d168, d4060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d168, d4060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d168, d4060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1388 p hg
    simpa only [d168, d4060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1390 (p : Pattern) (guard : d4058 p = 1) : d169 p ≤ (0 : Int) + d4061 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d169, d4061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d169, d4061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d169, d4061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1389 p hg
    simpa only [d169, d4061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1391 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare859 p hg
    simpa only [d97, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d97, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1392 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare860 p hg
    simpa only [d98, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1391 p hg
    simpa only [d98, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1393 (p : Pattern) (guard : d0 p = 1) : d208 p ≤ (0 : Int) + d208 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1394 (p : Pattern) (guard : d4058 p = 1) : d209 p ≤ (0 : Int) + d208 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1392 p hg
    simpa only [d4058, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1393 p hg
    simpa only [d4058, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1395 (p : Pattern) (guard : d4058 p = 1) : d210 p ≤ (0 : Int) + d4099 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d210, d4099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d210, d4099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d210, d4099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1394 p hg
    simpa only [d210, d4099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1396 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d114 p := by
  omega
theorem compare1397 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (0 : Int) + d117 p := by
  omega
theorem compare1398 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1397 p hg
    simpa only [d118, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1399 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d121 p := by
  omega
end NetHack.Sokoban22Refined85
