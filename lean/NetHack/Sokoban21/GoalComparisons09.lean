/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons08
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC1170 (pattern : Twelve) (guard : d3271 pattern = 1) : d1322 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1322 pattern).2
  change d1322 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1171 (pattern : Twelve) (guard : d3272 pattern = 1) : d1323 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1323, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1169 pattern childGuard
    simpa only [d3272, d1323, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1323, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1170 pattern childGuard
    simpa only [d3272, d1323, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1172 (pattern : Twelve) (guard : d3275 pattern = 1) : d1323 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1323 pattern).2
  change d1323 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1173 (pattern : Twelve) (guard : d3276 pattern = 1) : d1323 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1171 pattern childGuard
    simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1172 pattern childGuard
    simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1174 (pattern : Twelve) (guard : d3278 pattern = 1) : d1323 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1323 pattern).2
  change d1323 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1175 (pattern : Twelve) (guard : d3279 pattern = 1) : d1323 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1173 pattern childGuard
    simpa only [d3279, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1174 pattern childGuard
    simpa only [d3279, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1176 (pattern : Twelve) (guard : d3271 pattern = 1) : d1321 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1321 pattern).2
  change d1321 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1177 (pattern : Twelve) (guard : d3272 pattern = 1) : d1321 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1169 pattern childGuard
    simpa only [d3272, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1176 pattern childGuard
    simpa only [d3272, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1178 (pattern : Twelve) (guard : d3275 pattern = 1) : d1321 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1321 pattern).2
  change d1321 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1179 (pattern : Twelve) (guard : d3276 pattern = 1) : d1321 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1177 pattern childGuard
    simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1178 pattern childGuard
    simpa only [d3276, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1180 (pattern : Twelve) (guard : d3278 pattern = 1) : d1353 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1353 pattern).2
  change d1353 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1181 (pattern : Twelve) (guard : d3279 pattern = 1) : d1354 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1354, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1179 pattern childGuard
    simpa only [d3279, d1354, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1354, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1180 pattern childGuard
    simpa only [d3279, d1354, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1182 (pattern : Twelve) (guard : d3255 pattern = 1) : d1355 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC813 pattern childGuard
    simpa only [d3255, d1355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3255, d1355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1183 (pattern : Twelve) (guard : d3256 pattern = 1) : d1356 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC814 pattern childGuard
    simpa only [d3256, d1356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1182 pattern childGuard
    simpa only [d3256, d1356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1184 (pattern : Twelve) (guard : d3259 pattern = 1) : d1357 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC816 pattern childGuard
    simpa only [d3259, d1357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3259, d1357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1185 (pattern : Twelve) (guard : d3260 pattern = 1) : d1359 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1359, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1183 pattern childGuard
    simpa only [d3260, d1359, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1359, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1184 pattern childGuard
    simpa only [d3260, d1359, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1186 (pattern : Twelve) (guard : d3263 pattern = 1) : d1360 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1360, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1184 pattern childGuard
    simpa only [d3263, d1360, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1360, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3263, d1360, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1187 (pattern : Twelve) (guard : d3264 pattern = 1) : d1362 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1362, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1185 pattern childGuard
    simpa only [d3264, d1362, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1362, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1186 pattern childGuard
    simpa only [d3264, d1362, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1188 (pattern : Twelve) (guard : d3259 pattern = 1) : d1358 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC822 pattern childGuard
    simpa only [d3259, d1358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC197 pattern childGuard
    simpa only [d3259, d1358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1189 (pattern : Twelve) (guard : d3263 pattern = 1) : d1361 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1361, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1188 pattern childGuard
    simpa only [d3263, d1361, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1361, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3263, d1361, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1190 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1191 (pattern : Twelve) (guard : d3267 pattern = 1) : d1363 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1363, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1189 pattern childGuard
    simpa only [d3267, d1363, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1363, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1190 pattern childGuard
    simpa only [d3267, d1363, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1192 (pattern : Twelve) (guard : d3268 pattern = 1) : d1364 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1364, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1187 pattern childGuard
    simpa only [d3268, d1364, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1364, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1191 pattern childGuard
    simpa only [d3268, d1364, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1193 (pattern : Twelve) (guard : d3271 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC1194 (pattern : Twelve) (guard : d3272 pattern = 1) : d1365 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1365, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1192 pattern childGuard
    simpa only [d3272, d1365, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1365, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1193 pattern childGuard
    simpa only [d3272, d1365, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1195 (pattern : Twelve) (guard : d3275 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC1196 (pattern : Twelve) (guard : d3276 pattern = 1) : d1366 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1366, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1194 pattern childGuard
    simpa only [d3276, d1366, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1366, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1195 pattern childGuard
    simpa only [d3276, d1366, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1197 (pattern : Twelve) (guard : d3278 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC1198 (pattern : Twelve) (guard : d3279 pattern = 1) : d1367 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1367, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1196 pattern childGuard
    simpa only [d3279, d1367, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1367, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1197 pattern childGuard
    simpa only [d3279, d1367, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1199 (pattern : Twelve) (guard : d3264 pattern = 1) : d1368 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1368, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1153 pattern childGuard
    simpa only [d3264, d1368, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1368, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1186 pattern childGuard
    simpa only [d3264, d1368, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1200 (pattern : Twelve) (guard : d3267 pattern = 1) : d1369 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1369, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1166 pattern childGuard
    simpa only [d3267, d1369, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1369, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1190 pattern childGuard
    simpa only [d3267, d1369, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1201 (pattern : Twelve) (guard : d3268 pattern = 1) : d1373 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1373, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1199 pattern childGuard
    simpa only [d3268, d1373, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1373, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1200 pattern childGuard
    simpa only [d3268, d1373, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1202 (pattern : Twelve) (guard : d3271 pattern = 1) : d1374 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1374 pattern).2
  change d1374 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1203 (pattern : Twelve) (guard : d3272 pattern = 1) : d1376 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1376, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1201 pattern childGuard
    simpa only [d3272, d1376, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1376, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1202 pattern childGuard
    simpa only [d3272, d1376, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1204 (pattern : Twelve) (guard : d3275 pattern = 1) : d1377 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1377 pattern).2
  change d1377 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1205 (pattern : Twelve) (guard : d3276 pattern = 1) : d1378 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1378, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1203 pattern childGuard
    simpa only [d3276, d1378, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1378, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1204 pattern childGuard
    simpa only [d3276, d1378, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1206 (pattern : Twelve) (guard : d3278 pattern = 1) : d1377 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1377 pattern).2
  change d1377 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1207 (pattern : Twelve) (guard : d3279 pattern = 1) : d1379 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1379, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1205 pattern childGuard
    simpa only [d3279, d1379, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1379, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1206 pattern childGuard
    simpa only [d3279, d1379, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1208 (pattern : Twelve) (guard : d3251 pattern = 1) : d1380 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1139 pattern childGuard
    simpa only [d3251, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3251, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1209 (pattern : Twelve) (guard : d3252 pattern = 1) : d1385 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC846 pattern childGuard
    simpa only [d3252, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1208 pattern childGuard
    simpa only [d3252, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1210 (pattern : Twelve) (guard : d3251 pattern = 1) : d1381 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1144 pattern childGuard
    simpa only [d3251, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3251, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1211 (pattern : Twelve) (guard : d3255 pattern = 1) : d1386 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1210 pattern childGuard
    simpa only [d3255, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3255, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1212 (pattern : Twelve) (guard : d3256 pattern = 1) : d1393 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1209 pattern childGuard
    simpa only [d3256, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1211 pattern childGuard
    simpa only [d3256, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1213 (pattern : Twelve) (guard : d0 pattern = 1) : d1382 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1214 (pattern : Twelve) (guard : d3255 pattern = 1) : d1387 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC239 pattern childGuard
    simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1213 pattern childGuard
    simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1215 (pattern : Twelve) (guard : d0 pattern = 1) : d1388 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1216 (pattern : Twelve) (guard : d3259 pattern = 1) : d1394 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1214 pattern childGuard
    simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1215 pattern childGuard
    simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1217 (pattern : Twelve) (guard : d3260 pattern = 1) : d1398 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1398, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1212 pattern childGuard
    simpa only [d3260, d1398, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1398, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1216 pattern childGuard
    simpa only [d3260, d1398, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1218 (pattern : Twelve) (guard : d0 pattern = 1) : d1380 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1219 (pattern : Twelve) (guard : d3255 pattern = 1) : d1389 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC856 pattern childGuard
    simpa only [d3255, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1218 pattern childGuard
    simpa only [d3255, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1220 (pattern : Twelve) (guard : d0 pattern = 1) : d1386 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1221 (pattern : Twelve) (guard : d3259 pattern = 1) : d1395 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1219 pattern childGuard
    simpa only [d3259, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1220 pattern childGuard
    simpa only [d3259, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1222 (pattern : Twelve) (guard : d0 pattern = 1) : d1394 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1223 (pattern : Twelve) (guard : d3263 pattern = 1) : d1399 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1399, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1221 pattern childGuard
    simpa only [d3263, d1399, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1399, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1222 pattern childGuard
    simpa only [d3263, d1399, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1224 (pattern : Twelve) (guard : d3264 pattern = 1) : d1403 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1403, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1217 pattern childGuard
    simpa only [d3264, d1403, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1403, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1223 pattern childGuard
    simpa only [d3264, d1403, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1225 (pattern : Twelve) (guard : d0 pattern = 1) : d1382 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1226 (pattern : Twelve) (guard : d3255 pattern = 1) : d1387 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC260 pattern childGuard
    simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1225 pattern childGuard
    simpa only [d3255, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1227 (pattern : Twelve) (guard : d0 pattern = 1) : d1388 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1228 (pattern : Twelve) (guard : d3259 pattern = 1) : d1394 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1226 pattern childGuard
    simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1227 pattern childGuard
    simpa only [d3259, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1229 (pattern : Twelve) (guard : d0 pattern = 1) : d1396 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1230 (pattern : Twelve) (guard : d3263 pattern = 1) : d1400 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1400, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1228 pattern childGuard
    simpa only [d3263, d1400, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1400, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1229 pattern childGuard
    simpa only [d3263, d1400, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1231 (pattern : Twelve) (guard : d0 pattern = 1) : d1401 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1232 (pattern : Twelve) (guard : d3267 pattern = 1) : d1404 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1404, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1230 pattern childGuard
    simpa only [d3267, d1404, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1404, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1231 pattern childGuard
    simpa only [d3267, d1404, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1233 (pattern : Twelve) (guard : d3268 pattern = 1) : d1405 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1405, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1224 pattern childGuard
    simpa only [d3268, d1405, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1405, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1232 pattern childGuard
    simpa only [d3268, d1405, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1234 (pattern : Twelve) (guard : d3271 pattern = 1) : d1406 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1406 pattern).2
  change d1406 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1235 (pattern : Twelve) (guard : d3272 pattern = 1) : d1408 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1408, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1233 pattern childGuard
    simpa only [d3272, d1408, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1408, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1234 pattern childGuard
    simpa only [d3272, d1408, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1236 (pattern : Twelve) (guard : d3275 pattern = 1) : d1409 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1409 pattern).2
  change d1409 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1237 (pattern : Twelve) (guard : d3276 pattern = 1) : d1410 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1410, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1235 pattern childGuard
    simpa only [d3276, d1410, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1410, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1236 pattern childGuard
    simpa only [d3276, d1410, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1238 (pattern : Twelve) (guard : d3278 pattern = 1) : d1409 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1409 pattern).2
  change d1409 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1239 (pattern : Twelve) (guard : d3279 pattern = 1) : d1411 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1411, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1237 pattern childGuard
    simpa only [d3279, d1411, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1411, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1238 pattern childGuard
    simpa only [d3279, d1411, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1240 (pattern : Twelve) (guard : d3256 pattern = 1) : d1412 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1142 pattern childGuard
    simpa only [d3256, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1182 pattern childGuard
    simpa only [d3256, d1412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1241 (pattern : Twelve) (guard : d3259 pattern = 1) : d1413 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1150 pattern childGuard
    simpa only [d3259, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3259, d1413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1242 (pattern : Twelve) (guard : d3260 pattern = 1) : d1417 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1417, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1240 pattern childGuard
    simpa only [d3260, d1417, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1417, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1241 pattern childGuard
    simpa only [d3260, d1417, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1243 (pattern : Twelve) (guard : d3259 pattern = 1) : d1414 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1155 pattern childGuard
    simpa only [d3259, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3259, d1414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1244 (pattern : Twelve) (guard : d0 pattern = 1) : d1413 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1245 (pattern : Twelve) (guard : d3263 pattern = 1) : d1418 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1418, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1243 pattern childGuard
    simpa only [d3263, d1418, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1418, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1244 pattern childGuard
    simpa only [d3263, d1418, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1246 (pattern : Twelve) (guard : d3264 pattern = 1) : d1421 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1421, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1242 pattern childGuard
    simpa only [d3264, d1421, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1421, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1245 pattern childGuard
    simpa only [d3264, d1421, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1247 (pattern : Twelve) (guard : d3259 pattern = 1) : d1415 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1162 pattern childGuard
    simpa only [d3259, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC197 pattern childGuard
    simpa only [d3259, d1415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1248 (pattern : Twelve) (guard : d0 pattern = 1) : d1416 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1249 (pattern : Twelve) (guard : d3263 pattern = 1) : d1419 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1419, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1247 pattern childGuard
    simpa only [d3263, d1419, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1419, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1248 pattern childGuard
    simpa only [d3263, d1419, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1250 (pattern : Twelve) (guard : d0 pattern = 1) : d1420 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1251 (pattern : Twelve) (guard : d3267 pattern = 1) : d1422 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d1422, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1249 pattern childGuard
    simpa only [d3267, d1422, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d1422, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1250 pattern childGuard
    simpa only [d3267, d1422, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1252 (pattern : Twelve) (guard : d3268 pattern = 1) : d1423 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1423, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1246 pattern childGuard
    simpa only [d3268, d1423, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1423, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1251 pattern childGuard
    simpa only [d3268, d1423, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1253 (pattern : Twelve) (guard : d3271 pattern = 1) : d1424 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1424 pattern).2
  change d1424 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1254 (pattern : Twelve) (guard : d3272 pattern = 1) : d1425 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1425, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1252 pattern childGuard
    simpa only [d3272, d1425, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1425, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1253 pattern childGuard
    simpa only [d3272, d1425, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1255 (pattern : Twelve) (guard : d3275 pattern = 1) : d1424 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1424 pattern).2
  change d1424 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1256 (pattern : Twelve) (guard : d3276 pattern = 1) : d1426 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1426, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1254 pattern childGuard
    simpa only [d3276, d1426, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1426, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1255 pattern childGuard
    simpa only [d3276, d1426, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1257 (pattern : Twelve) (guard : d3278 pattern = 1) : d1424 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1424 pattern).2
  change d1424 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1258 (pattern : Twelve) (guard : d3279 pattern = 1) : d1427 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1427, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1256 pattern childGuard
    simpa only [d3279, d1427, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1427, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1257 pattern childGuard
    simpa only [d3279, d1427, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1259 (pattern : Twelve) (guard : d3268 pattern = 1) : d1428 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1428, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1160 pattern childGuard
    simpa only [d3268, d1428, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1428, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1191 pattern childGuard
    simpa only [d3268, d1428, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1260 (pattern : Twelve) (guard : d3271 pattern = 1) : d1429 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1429 pattern).2
  change d1429 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1261 (pattern : Twelve) (guard : d3272 pattern = 1) : d1431 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1431, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1259 pattern childGuard
    simpa only [d3272, d1431, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1431, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1260 pattern childGuard
    simpa only [d3272, d1431, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1262 (pattern : Twelve) (guard : d3275 pattern = 1) : d1432 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1432 pattern).2
  change d1432 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1263 (pattern : Twelve) (guard : d3276 pattern = 1) : d1433 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1433, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1261 pattern childGuard
    simpa only [d3276, d1433, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1433, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1262 pattern childGuard
    simpa only [d3276, d1433, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1264 (pattern : Twelve) (guard : d3278 pattern = 1) : d1432 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1432 pattern).2
  change d1432 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1265 (pattern : Twelve) (guard : d3279 pattern = 1) : d1434 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1434, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1263 pattern childGuard
    simpa only [d3279, d1434, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1434, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1264 pattern childGuard
    simpa only [d3279, d1434, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1266 (pattern : Twelve) (guard : d3260 pattern = 1) : d1435 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1435, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1148 pattern childGuard
    simpa only [d3260, d1435, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1435, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1184 pattern childGuard
    simpa only [d3260, d1435, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1267 (pattern : Twelve) (guard : d3263 pattern = 1) : d1436 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1436, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1157 pattern childGuard
    simpa only [d3263, d1436, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1436, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3263, d1436, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1268 (pattern : Twelve) (guard : d3264 pattern = 1) : d1438 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1438, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1266 pattern childGuard
    simpa only [d3264, d1438, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1438, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1267 pattern childGuard
    simpa only [d3264, d1438, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1269 (pattern : Twelve) (guard : d0 pattern = 1) : d1284 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1270 (pattern : Twelve) (guard : d3255 pattern = 1) : d1293 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC916 pattern childGuard
    simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1269 pattern childGuard
    simpa only [d3255, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1271 (pattern : Twelve) (guard : d0 pattern = 1) : d1294 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1272 (pattern : Twelve) (guard : d3259 pattern = 1) : d1305 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1270 pattern childGuard
    simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1271 pattern childGuard
    simpa only [d3259, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1273 (pattern : Twelve) (guard : d3263 pattern = 1) : d1436 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1436, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1272 pattern childGuard
    simpa only [d3263, d1436, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1436, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3263, d1436, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1274 (pattern : Twelve) (guard : d0 pattern = 1) : d1436 pattern ≤ (0 : Int) + d3287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1275 (pattern : Twelve) (guard : d3267 pattern = 1) : d1436 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3267, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1273 pattern childGuard
    simpa only [d3267, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3267, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1274 pattern childGuard
    simpa only [d3267, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1276 (pattern : Twelve) (guard : d3268 pattern = 1) : d1439 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3268, d1439, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1268 pattern childGuard
    simpa only [d3268, d1439, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3267 pattern = 1 := by simpa only [d3268, d1439, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1275 pattern childGuard
    simpa only [d3268, d1439, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1277 (pattern : Twelve) (guard : d3271 pattern = 1) : d1437 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1437 pattern).2
  change d1437 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1278 (pattern : Twelve) (guard : d3272 pattern = 1) : d1440 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3272, d1440, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1276 pattern childGuard
    simpa only [d3272, d1440, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3271 pattern = 1 := by simpa only [d3272, d1440, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1277 pattern childGuard
    simpa only [d3272, d1440, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1279 (pattern : Twelve) (guard : d3275 pattern = 1) : d1441 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1441 pattern).2
  change d1441 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1280 (pattern : Twelve) (guard : d3276 pattern = 1) : d1442 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3276, d1442, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1278 pattern childGuard
    simpa only [d3276, d1442, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3275 pattern = 1 := by simpa only [d3276, d1442, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1279 pattern childGuard
    simpa only [d3276, d1442, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1281 (pattern : Twelve) (guard : d3278 pattern = 1) : d1441 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1441 pattern).2
  change d1441 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1282 (pattern : Twelve) (guard : d3279 pattern = 1) : d1443 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3279, d1443, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1280 pattern childGuard
    simpa only [d3279, d1443, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3278 pattern = 1 := by simpa only [d3279, d1443, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1281 pattern childGuard
    simpa only [d3279, d1443, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1283 (pattern : Twelve) (guard : d3247 pattern = 1) : d1444 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d1444, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1138 pattern childGuard
    simpa only [d3247, d1444, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d1444, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d3247, d1444, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1284 (pattern : Twelve) (guard : d0 pattern = 1) : d1280 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1285 (pattern : Twelve) (guard : d3251 pattern = 1) : d1445 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1283 pattern childGuard
    simpa only [d3251, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1284 pattern childGuard
    simpa only [d3251, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1286 (pattern : Twelve) (guard : d3252 pattern = 1) : d1448 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC937 pattern childGuard
    simpa only [d3252, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1285 pattern childGuard
    simpa only [d3252, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1287 (pattern : Twelve) (guard : d0 pattern = 1) : d29 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1288 (pattern : Twelve) (guard : d3251 pattern = 1) : d29 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC20 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1287 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1289 (pattern : Twelve) (guard : d3255 pattern = 1) : d1449 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1288 pattern childGuard
    simpa only [d3255, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3255, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1290 (pattern : Twelve) (guard : d3256 pattern = 1) : d1455 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1286 pattern childGuard
    simpa only [d3256, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1289 pattern childGuard
    simpa only [d3256, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1291 (pattern : Twelve) (guard : d0 pattern = 1) : d1445 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1292 (pattern : Twelve) (guard : d3255 pattern = 1) : d1450 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC943 pattern childGuard
    simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1291 pattern childGuard
    simpa only [d3255, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1293 (pattern : Twelve) (guard : d0 pattern = 1) : d1449 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1294 (pattern : Twelve) (guard : d3259 pattern = 1) : d1456 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1292 pattern childGuard
    simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1293 pattern childGuard
    simpa only [d3259, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1295 (pattern : Twelve) (guard : d3260 pattern = 1) : d1459 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1459, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1290 pattern childGuard
    simpa only [d3260, d1459, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1459, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1294 pattern childGuard
    simpa only [d3260, d1459, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1296 (pattern : Twelve) (guard : d0 pattern = 1) : d1456 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1297 (pattern : Twelve) (guard : d3263 pattern = 1) : d1456 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1294 pattern childGuard
    simpa only [d3263, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1296 pattern childGuard
    simpa only [d3263, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1298 (pattern : Twelve) (guard : d3264 pattern = 1) : d1463 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1463, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1295 pattern childGuard
    simpa only [d3264, d1463, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1463, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1297 pattern childGuard
    simpa only [d3264, d1463, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1299 (pattern : Twelve) (guard : d0 pattern = 1) : d1445 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
