/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons093
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c13160 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13158 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13159 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13161 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (5 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13157 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13160 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13162 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (5 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13156 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13161 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13163 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (5 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13150 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13162 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13164 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (5 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13142 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13165 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (5 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13163 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13164 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13166 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (5 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13143 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13165 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13167 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (5 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12976 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13004 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13168 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (5 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13167 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13129 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13169 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (5 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13118 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13168 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13170 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (5 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13113 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13171 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (5 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13135 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13170 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13172 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (5 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13028 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13171 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13173 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (5 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13016 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13050 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13174 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (5 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13173 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13129 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13175 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (5 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13172 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13174 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13176 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (5 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13169 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13175 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13177 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (5 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13113 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13145 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13178 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (5 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13135 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13177 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13179 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (5 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13178 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13180 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (5 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13016 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13044 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13181 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (5 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13180 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13129 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13182 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (5 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13179 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13181 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13183 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (5 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13145 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13184 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (5 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13152 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13183 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13185 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (5 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13051 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13184 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13186 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (5 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13043 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13187 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (5 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13055 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13186 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13188 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (5 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13187 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13160 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13189 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (5 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13185 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13188 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13190 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (5 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13182 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13189 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13191 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (5 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13175 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13192 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (5 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13190 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13191 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13193 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (5 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13176 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13192 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13194 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (5 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13166 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13193 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13195 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (5 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12975 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12979 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13196 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (5 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12965 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13197 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (5 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13196 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12979 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13198 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (5 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13195 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13197 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13199 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (5 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13198 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13197 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13200 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (5 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12976 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13199 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13201 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (5 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12987 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13202 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (5 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13200 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13201 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13203 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (5 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13132 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13204 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (5 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12982 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13203 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13205 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (5 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13195 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13204 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13206 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (5 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13197 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13207 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (5 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13205 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13206 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13208 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (5 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13140 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13207 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13209 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (5 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12987 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13058 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13210 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (5 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12989 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13211 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (5 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13210 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13212 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (5 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13208 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13211 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13213 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (5 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13202 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13212 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13214 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13033 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13215 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (5 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13214 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13203 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13216 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (5 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13197 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13215 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13217 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (5 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13205 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13216 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13218 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (5 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13016 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13217 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13219 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (5 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13220 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (5 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13218 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13219 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13221 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (5 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13053 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13006 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13222 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (5 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13204 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13221 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13223 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (5 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13215 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13224 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (5 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13222 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13223 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13225 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (5 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13157 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13224 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13226 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (5 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13058 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13227 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (5 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13226 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13059 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13228 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (5 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13227 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13229 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (5 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13225 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13228 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13230 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (5 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13220 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13229 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13231 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (5 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13212 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13232 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (5 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13230 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13231 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13233 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (5 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13213 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13232 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13234 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (5 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12987 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13015 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13235 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (5 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13234 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13236 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (5 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13200 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13235 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13237 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (5 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13075 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13238 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (5 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13237 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13239 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (5 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13208 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13238 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13240 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (5 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13236 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13239 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13241 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (5 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13055 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13242 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (5 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13241 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13243 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (5 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13218 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13242 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13244 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (5 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13226 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13101 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13245 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (5 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13244 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13246 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (5 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13225 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13245 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13247 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (5 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13243 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13246 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13248 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (5 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13239 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13249 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (5 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13247 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13248 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13250 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (5 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13240 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13249 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13251 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (5 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13233 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13250 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13252 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13123 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13125 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13253 (pattern : Twelve) (guard : d1 pattern = 1) : d1649 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13124 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13252 pattern childGuard
    simpa only [d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13254 (pattern : Twelve) (guard : d1 pattern = 1) : d1650 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13126 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13255 (pattern : Twelve) (guard : d1 pattern = 1) : d1656 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13253 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13254 pattern childGuard
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13256 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13124 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13257 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13127 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13256 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13258 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13252 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12999 pattern childGuard
    simpa only [d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13259 (pattern : Twelve) (guard : d1 pattern = 1) : d1645 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13252 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13260 (pattern : Twelve) (guard : d1 pattern = 1) : d1647 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13258 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13259 pattern childGuard
    simpa only [d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13261 (pattern : Twelve) (guard : d1 pattern = 1) : d1651 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13257 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13260 pattern childGuard
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13262 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13158 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13128 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13263 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13262 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13264 (pattern : Twelve) (guard : d1 pattern = 1) : d1657 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13261 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13263 pattern childGuard
    simpa only [d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13265 (pattern : Twelve) (guard : d1 pattern = 1) : d1660 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13255 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13264 pattern childGuard
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13266 (pattern : Twelve) (guard : d1 pattern = 1) : d1652 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13127 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13258 pattern childGuard
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13267 (pattern : Twelve) (guard : d1 pattern = 1) : d1653 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13158 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13268 (pattern : Twelve) (guard : d1 pattern = 1) : d1658 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13266 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13267 pattern childGuard
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13269 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12999 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13011 pattern childGuard
    simpa only [d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13270 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12999 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13271 (pattern : Twelve) (guard : d1 pattern = 1) : d1648 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13269 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13270 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13272 (pattern : Twelve) (guard : d1 pattern = 1) : d1654 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13262 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13271 pattern childGuard
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13273 (pattern : Twelve) (guard : d1 pattern = 1) : d1655 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13159 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13274 (pattern : Twelve) (guard : d1 pattern = 1) : d1659 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13272 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13273 pattern childGuard
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13275 (pattern : Twelve) (guard : d1 pattern = 1) : d1661 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13268 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13274 pattern childGuard
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13276 (pattern : Twelve) (guard : d1 pattern = 1) : d1662 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13264 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13277 (pattern : Twelve) (guard : d1 pattern = 1) : d1663 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13275 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13276 pattern childGuard
    simpa only [d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13278 (pattern : Twelve) (guard : d1 pattern = 1) : d1664 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13265 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13277 pattern childGuard
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13279 (pattern : Twelve) (guard : d0 pattern = 1) : d110 pattern ≤ (2 : Int) + d103 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c13280 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d0 pattern := by
  omega
theorem c13281 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d0 pattern := by
  change (2 : Int) ≤ (2 : Int) + 0
  decide
theorem c13282 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13283 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d1 pattern := by
  change (2 : Int) ≤ (2 : Int) + 1
  decide
theorem c13284 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (2 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13283 pattern childGuard
    simpa only [d30, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13285 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (2 : Int) + d17 pattern := by
  omega
theorem c13286 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d1 pattern := by
  change (3 : Int) ≤ (2 : Int) + 1
  decide
theorem c13287 (pattern : Twelve) (guard : d1 pattern = 1) : d37 pattern ≤ (2 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d37, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13288 (pattern : Twelve) (guard : d1 pattern = 1) : d58 pattern ≤ (2 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13284 pattern childGuard
    simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13287 pattern childGuard
    simpa only [d58, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13289 (pattern : Twelve) (guard : d1 pattern = 1) : d79 pattern ≤ (2 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13282 pattern childGuard
    simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13288 pattern childGuard
    simpa only [d79, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13290 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (2 : Int) + d55 pattern := by
  omega
theorem c13291 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (2 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13282 pattern childGuard
    simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13290 pattern childGuard
    simpa only [d80, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13292 (pattern : Twelve) (guard : d1 pattern = 1) : d95 pattern ≤ (2 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13289 pattern childGuard
    simpa only [d95, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d95, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13291 pattern childGuard
    simpa only [d95, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13293 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d2 pattern := by
  change (4 : Int) ≤ (2 : Int) + 2
  decide
theorem c13294 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13293 pattern childGuard
    simpa only [d38, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13295 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d6 pattern := by
  omega
theorem c13296 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (2 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13295 pattern childGuard
    simpa only [d39, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13297 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13294 pattern childGuard
    simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13296 pattern childGuard
    simpa only [d59, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13298 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d9, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13286 pattern childGuard
    simpa only [d9, d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13299 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13281 pattern childGuard
    simpa only [d23, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13298 pattern childGuard
    simpa only [d23, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
