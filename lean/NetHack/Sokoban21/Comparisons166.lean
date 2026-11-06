/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons165
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c23240 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (20 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23238 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23239 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23241 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (20 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23220 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23240 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23242 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (20 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23243 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (20 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23242 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23207 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23244 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (20 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23196 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23243 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23245 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (20 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23108 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23246 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (20 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23212 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23245 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23247 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (20 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23025 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23246 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23248 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (20 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23047 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23249 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (20 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23248 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23207 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23250 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (20 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23247 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23249 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23251 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (20 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23244 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23250 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23252 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (20 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23108 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23132 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23253 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (20 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23212 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23252 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23254 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (20 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23253 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23255 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (20 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23041 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23256 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (20 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23255 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23207 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23257 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (20 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23254 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23256 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23258 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (20 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23227 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23148 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23259 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (20 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23048 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23258 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23260 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (20 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23052 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23176 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23261 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (20 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23260 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23235 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23262 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (20 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23259 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23261 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23263 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (20 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23257 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23262 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23264 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (20 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23250 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23265 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (20 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23263 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23264 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23266 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (20 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23251 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23265 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23267 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (20 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23241 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23266 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23268 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (20 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22962 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22971 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23269 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (20 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23268 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22976 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23270 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (20 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23191 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23271 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (20 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23193 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23272 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (20 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23270 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23271 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23273 (pattern : Twelve) (guard : d1 pattern = 1) : d890 pattern ≤ (20 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23272 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23274 (pattern : Twelve) (guard : d1 pattern = 1) : d876 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23202 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23004 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23275 (pattern : Twelve) (guard : d1 pattern = 1) : d883 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23274 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23206 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23276 (pattern : Twelve) (guard : d1 pattern = 1) : d891 pattern ≤ (20 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23275 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23277 (pattern : Twelve) (guard : d1 pattern = 1) : d898 pattern ≤ (20 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23273 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23276 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23278 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (20 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23191 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23228 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23279 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (20 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23278 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23213 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23280 (pattern : Twelve) (guard : d1 pattern = 1) : d892 pattern ≤ (20 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23025 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23279 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23281 (pattern : Twelve) (guard : d1 pattern = 1) : d893 pattern ≤ (20 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23217 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23275 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23282 (pattern : Twelve) (guard : d1 pattern = 1) : d899 pattern ≤ (20 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23280 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23281 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23283 (pattern : Twelve) (guard : d1 pattern = 1) : d902 pattern ≤ (20 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23277 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23282 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23284 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (20 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23193 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23226 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23285 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (20 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23278 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23284 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23286 (pattern : Twelve) (guard : d1 pattern = 1) : d894 pattern ≤ (20 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23285 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23287 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (20 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23030 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22978 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23288 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (20 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23130 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22994 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23289 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (20 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23287 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23288 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23290 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (20 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23289 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23291 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (20 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23290 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23292 (pattern : Twelve) (guard : d1 pattern = 1) : d895 pattern ≤ (20 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23291 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23275 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23293 (pattern : Twelve) (guard : d1 pattern = 1) : d900 pattern ≤ (20 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23286 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23292 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23294 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (20 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23211 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23295 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (20 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23141 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23050 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23296 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (20 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23295 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23297 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (20 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23294 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23296 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23298 (pattern : Twelve) (guard : d1 pattern = 1) : d896 pattern ≤ (20 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23048 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23297 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23299 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (20 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23139 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23300 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (20 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23289 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23301 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (20 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23299 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23300 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23302 (pattern : Twelve) (guard : d1 pattern = 1) : d889 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23206 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23303 (pattern : Twelve) (guard : d1 pattern = 1) : d897 pattern ≤ (20 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23301 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23302 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23304 (pattern : Twelve) (guard : d1 pattern = 1) : d901 pattern ≤ (20 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23298 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23303 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23305 (pattern : Twelve) (guard : d1 pattern = 1) : d903 pattern ≤ (20 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23293 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23304 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23306 (pattern : Twelve) (guard : d1 pattern = 1) : d904 pattern ≤ (20 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23282 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23307 (pattern : Twelve) (guard : d1 pattern = 1) : d905 pattern ≤ (20 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23305 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23306 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23308 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (20 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23283 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23307 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23309 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (20 : Int) + d1616 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23211 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23132 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23310 (pattern : Twelve) (guard : d1 pattern = 1) : d1247 pattern ≤ (20 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23228 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23132 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23311 (pattern : Twelve) (guard : d1 pattern = 1) : d1249 pattern ≤ (20 : Int) + d1619 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23309 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23310 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23312 (pattern : Twelve) (guard : d1 pattern = 1) : d1253 pattern ≤ (20 : Int) + d1622 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23311 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23313 (pattern : Twelve) (guard : d1 pattern = 1) : d1248 pattern ≤ (20 : Int) + d1617 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23040 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23314 (pattern : Twelve) (guard : d1 pattern = 1) : d1254 pattern ≤ (20 : Int) + d1623 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23313 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23235 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23315 (pattern : Twelve) (guard : d1 pattern = 1) : d1258 pattern ≤ (20 : Int) + d1627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23312 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23314 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23316 (pattern : Twelve) (guard : d1 pattern = 1) : d1261 pattern ≤ (20 : Int) + d1630 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23315 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23262 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23317 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (20 : Int) + d1618 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23132 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23146 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23318 (pattern : Twelve) (guard : d1 pattern = 1) : d1250 pattern ≤ (20 : Int) + d1620 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23227 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23317 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23319 (pattern : Twelve) (guard : d1 pattern = 1) : d1255 pattern ≤ (20 : Int) + d1624 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23041 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23318 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23320 (pattern : Twelve) (guard : d1 pattern = 1) : d1259 pattern ≤ (20 : Int) + d1628 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23319 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23261 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23321 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (20 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23226 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23322 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (20 : Int) + d182 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23146 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23323 (pattern : Twelve) (guard : d1 pattern = 1) : d1251 pattern ≤ (20 : Int) + d1621 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23321 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23322 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23324 (pattern : Twelve) (guard : d1 pattern = 1) : d1256 pattern ≤ (20 : Int) + d1625 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23176 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23323 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23325 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23234 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23326 (pattern : Twelve) (guard : d1 pattern = 1) : d1257 pattern ≤ (20 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23181 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23325 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23327 (pattern : Twelve) (guard : d1 pattern = 1) : d1260 pattern ≤ (20 : Int) + d1629 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23324 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23326 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23328 (pattern : Twelve) (guard : d1 pattern = 1) : d1262 pattern ≤ (20 : Int) + d1631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23320 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23327 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23329 (pattern : Twelve) (guard : d1 pattern = 1) : d1263 pattern ≤ (20 : Int) + d1632 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23262 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23330 (pattern : Twelve) (guard : d1 pattern = 1) : d1264 pattern ≤ (20 : Int) + d1633 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23328 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23329 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23331 (pattern : Twelve) (guard : d1 pattern = 1) : d1265 pattern ≤ (20 : Int) + d1634 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23316 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23330 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23332 (pattern : Twelve) (guard : d1 pattern = 1) : d1266 pattern ≤ (20 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23308 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23331 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23333 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (20 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23267 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23332 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23334 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (20 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22972 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22976 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23335 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (20 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23334 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23336 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (20 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23335 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23337 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (20 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23336 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23338 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (20 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22984 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23339 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (20 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23337 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23338 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23340 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (20 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22979 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23288 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23341 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (20 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23334 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23340 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23342 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (20 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23343 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (20 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23341 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23342 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23344 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (20 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23217 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23343 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23345 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (20 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22984 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23055 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23346 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (20 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23345 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22986 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23347 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (20 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23346 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23348 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (20 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23344 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23347 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23349 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (20 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23339 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23348 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23350 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (20 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23269 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23289 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23351 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (20 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23341 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23350 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23352 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (20 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23351 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23353 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (20 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23345 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23354 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (20 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23352 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23353 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23355 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (20 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23050 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23003 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23356 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (20 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23340 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23355 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23357 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (20 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23356 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23300 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23358 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (20 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23232 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23357 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23359 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (20 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23055 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23004 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23360 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (20 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23359 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23056 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23361 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (20 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23360 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23362 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (20 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23358 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23361 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23363 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (20 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23354 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23362 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23364 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (20 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23348 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23365 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (20 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23363 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23364 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23366 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (20 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23349 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23365 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23367 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (20 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22984 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23368 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (20 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23367 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23369 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (20 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23337 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23368 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23370 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (20 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23345 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23072 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23371 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (20 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23370 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23372 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (20 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23344 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23371 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23373 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (20 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23369 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23372 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23374 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (20 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23345 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23052 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23375 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (20 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23374 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23376 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (20 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23352 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23375 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23377 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (20 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23359 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23098 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23378 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (20 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23377 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23379 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (20 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23358 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23378 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
