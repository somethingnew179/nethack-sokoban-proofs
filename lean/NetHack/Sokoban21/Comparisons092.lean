/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons091
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c12880 (pattern : Twelve) (guard : d1865 pattern = 1) : d1277 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12584 pattern childGuard
    simpa only [d1865, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12697 pattern childGuard
    simpa only [d1865, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12881 (pattern : Twelve) (guard : d1865 pattern = 1) : d1282 pattern ≤ (1 : Int) + d2203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1282, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12866 pattern childGuard
    simpa only [d1282, d2203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1282, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12880 pattern childGuard
    simpa only [d1282, d2203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12882 (pattern : Twelve) (guard : d1865 pattern = 1) : d1288 pattern ≤ (1 : Int) + d2204 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1288, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12881 pattern childGuard
    simpa only [d1288, d2204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1288, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12771 pattern childGuard
    simpa only [d1288, d2204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12883 (pattern : Twelve) (guard : d1865 pattern = 1) : d1299 pattern ≤ (1 : Int) + d2205 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1299, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12811 pattern childGuard
    simpa only [d1299, d2205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1299, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12882 pattern childGuard
    simpa only [d1299, d2205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12884 (pattern : Twelve) (guard : d1865 pattern = 1) : d1289 pattern ≤ (1 : Int) + d2206 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1289, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12812 pattern childGuard
    simpa only [d1289, d2206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1289, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12737 pattern childGuard
    simpa only [d1289, d2206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12885 (pattern : Twelve) (guard : d1865 pattern = 1) : d1300 pattern ≤ (1 : Int) + d2207 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1300, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12884 pattern childGuard
    simpa only [d1300, d2207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1300, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1300, d2207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12886 (pattern : Twelve) (guard : d1865 pattern = 1) : d1308 pattern ≤ (1 : Int) + d2208 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1308, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12883 pattern childGuard
    simpa only [d1308, d2208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1308, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12885 pattern childGuard
    simpa only [d1308, d2208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12887 (pattern : Twelve) (guard : d1865 pattern = 1) : d1314 pattern ≤ (1 : Int) + d2209 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1314, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12879 pattern childGuard
    simpa only [d1314, d2209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1314, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12886 pattern childGuard
    simpa only [d1314, d2209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12888 (pattern : Twelve) (guard : d1865 pattern = 1) : d1315 pattern ≤ (1 : Int) + d2210 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1315, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12873 pattern childGuard
    simpa only [d1315, d2210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1315, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1315, d2210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12889 (pattern : Twelve) (guard : d1865 pattern = 1) : d1319 pattern ≤ (1 : Int) + d2211 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1319, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12887 pattern childGuard
    simpa only [d1319, d2211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1319, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12888 pattern childGuard
    simpa only [d1319, d2211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12890 (pattern : Twelve) (guard : d1865 pattern = 1) : d1321 pattern ≤ (1 : Int) + d2212 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1321, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12874 pattern childGuard
    simpa only [d1321, d2212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1321, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12889 pattern childGuard
    simpa only [d1321, d2212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12891 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11213 pattern childGuard
    simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d11, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12892 (pattern : Twelve) (guard : d0 pattern = 1) : d16 pattern ≤ (1 : Int) + d16 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12893 (pattern : Twelve) (guard : d1865 pattern = 1) : d1324 pattern ≤ (1 : Int) + d16 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12891 pattern childGuard
    simpa only [d1865, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12892 pattern childGuard
    simpa only [d1865, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12894 (pattern : Twelve) (guard : d1865 pattern = 1) : d1325 pattern ≤ (1 : Int) + d2213 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1325, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12859 pattern childGuard
    simpa only [d1325, d2213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1325, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12893 pattern childGuard
    simpa only [d1325, d2213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12895 (pattern : Twelve) (guard : d1865 pattern = 1) : d1326 pattern ≤ (1 : Int) + d2213 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1326, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d1326, d2213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1326, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12893 pattern childGuard
    simpa only [d1326, d2213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12896 (pattern : Twelve) (guard : d1865 pattern = 1) : d1333 pattern ≤ (1 : Int) + d2213 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12894 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12895 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12897 (pattern : Twelve) (guard : d1865 pattern = 1) : d1339 pattern ≤ (1 : Int) + d2214 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1339, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d1339, d2214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1339, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12896 pattern childGuard
    simpa only [d1339, d2214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12898 (pattern : Twelve) (guard : d1865 pattern = 1) : d1345 pattern ≤ (1 : Int) + d2215 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1345, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12897 pattern childGuard
    simpa only [d1345, d2215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1345, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12863 pattern childGuard
    simpa only [d1345, d2215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12899 (pattern : Twelve) (guard : d1865 pattern = 1) : d1327 pattern ≤ (1 : Int) + d2192 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1327, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12859 pattern childGuard
    simpa only [d1327, d2192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1327, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12770 pattern childGuard
    simpa only [d1327, d2192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12900 (pattern : Twelve) (guard : d1865 pattern = 1) : d1334 pattern ≤ (1 : Int) + d2194 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1334, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12899 pattern childGuard
    simpa only [d1334, d2194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1334, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12868 pattern childGuard
    simpa only [d1334, d2194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12901 (pattern : Twelve) (guard : d1865 pattern = 1) : d1340 pattern ≤ (1 : Int) + d2195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1340, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12797 pattern childGuard
    simpa only [d1340, d2195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1340, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12900 pattern childGuard
    simpa only [d1340, d2195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12902 (pattern : Twelve) (guard : d1865 pattern = 1) : d1346 pattern ≤ (1 : Int) + d2198 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1346, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12901 pattern childGuard
    simpa only [d1346, d2198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1346, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12872 pattern childGuard
    simpa only [d1346, d2198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12903 (pattern : Twelve) (guard : d1865 pattern = 1) : d1349 pattern ≤ (1 : Int) + d2216 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1349, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12898 pattern childGuard
    simpa only [d1349, d2216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1349, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12902 pattern childGuard
    simpa only [d1349, d2216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12904 (pattern : Twelve) (guard : d1865 pattern = 1) : d1328 pattern ≤ (1 : Int) + d2217 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1328, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d1328, d2217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1328, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12880 pattern childGuard
    simpa only [d1328, d2217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12905 (pattern : Twelve) (guard : d1865 pattern = 1) : d1335 pattern ≤ (1 : Int) + d2218 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1335, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12899 pattern childGuard
    simpa only [d1335, d2218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1335, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12904 pattern childGuard
    simpa only [d1335, d2218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12906 (pattern : Twelve) (guard : d1865 pattern = 1) : d1341 pattern ≤ (1 : Int) + d2219 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1341, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d1341, d2219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1341, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12905 pattern childGuard
    simpa only [d1341, d2219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12907 (pattern : Twelve) (guard : d1865 pattern = 1) : d1329 pattern ≤ (1 : Int) + d2220 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1329, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12687 pattern childGuard
    simpa only [d1329, d2220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1329, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12694 pattern childGuard
    simpa only [d1329, d2220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12908 (pattern : Twelve) (guard : d1865 pattern = 1) : d1336 pattern ≤ (1 : Int) + d2221 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1336, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12790 pattern childGuard
    simpa only [d1336, d2221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1336, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12907 pattern childGuard
    simpa only [d1336, d2221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12909 (pattern : Twelve) (guard : d1865 pattern = 1) : d1342 pattern ≤ (1 : Int) + d2222 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1342, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12908 pattern childGuard
    simpa only [d1342, d2222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1342, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1342, d2222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12910 (pattern : Twelve) (guard : d1865 pattern = 1) : d1347 pattern ≤ (1 : Int) + d2223 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1347, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12906 pattern childGuard
    simpa only [d1347, d2223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1347, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12909 pattern childGuard
    simpa only [d1347, d2223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12911 (pattern : Twelve) (guard : d1865 pattern = 1) : d1330 pattern ≤ (1 : Int) + d2116 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1330, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12866 pattern childGuard
    simpa only [d1330, d2116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1330, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1330, d2116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12912 (pattern : Twelve) (guard : d1865 pattern = 1) : d1331 pattern ≤ (1 : Int) + d2148 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1331, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12880 pattern childGuard
    simpa only [d1331, d2148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1331, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1331, d2148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12913 (pattern : Twelve) (guard : d1865 pattern = 1) : d1337 pattern ≤ (1 : Int) + d2224 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1337, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12911 pattern childGuard
    simpa only [d1337, d2224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1337, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12912 pattern childGuard
    simpa only [d1337, d2224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12914 (pattern : Twelve) (guard : d1865 pattern = 1) : d1343 pattern ≤ (1 : Int) + d2225 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1343, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12811 pattern childGuard
    simpa only [d1343, d2225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1343, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12913 pattern childGuard
    simpa only [d1343, d2225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12915 (pattern : Twelve) (guard : d1865 pattern = 1) : d1332 pattern ≤ (1 : Int) + d2088 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1332, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12736 pattern childGuard
    simpa only [d1332, d2088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1332, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d1332, d2088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12916 (pattern : Twelve) (guard : d1865 pattern = 1) : d1338 pattern ≤ (1 : Int) + d2226 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1338, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12915 pattern childGuard
    simpa only [d1338, d2226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1338, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12776 pattern childGuard
    simpa only [d1338, d2226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12917 (pattern : Twelve) (guard : d1865 pattern = 1) : d1344 pattern ≤ (1 : Int) + d2227 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1344, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12916 pattern childGuard
    simpa only [d1344, d2227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1344, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1344, d2227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12918 (pattern : Twelve) (guard : d1865 pattern = 1) : d1348 pattern ≤ (1 : Int) + d2228 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1348, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12914 pattern childGuard
    simpa only [d1348, d2228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1348, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12917 pattern childGuard
    simpa only [d1348, d2228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12919 (pattern : Twelve) (guard : d1865 pattern = 1) : d1350 pattern ≤ (1 : Int) + d2229 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1350, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12910 pattern childGuard
    simpa only [d1350, d2229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1350, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12918 pattern childGuard
    simpa only [d1350, d2229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12920 (pattern : Twelve) (guard : d1865 pattern = 1) : d1351 pattern ≤ (1 : Int) + d2210 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1351, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12902 pattern childGuard
    simpa only [d1351, d2210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1351, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1351, d2210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12921 (pattern : Twelve) (guard : d1865 pattern = 1) : d1352 pattern ≤ (1 : Int) + d2230 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1352, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12919 pattern childGuard
    simpa only [d1352, d2230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1352, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12920 pattern childGuard
    simpa only [d1352, d2230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12922 (pattern : Twelve) (guard : d1865 pattern = 1) : d1353 pattern ≤ (1 : Int) + d2231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1353, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12903 pattern childGuard
    simpa only [d1353, d2231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1353, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12921 pattern childGuard
    simpa only [d1353, d2231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12923 (pattern : Twelve) (guard : d1865 pattern = 1) : d1354 pattern ≤ (1 : Int) + d2232 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1354, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12890 pattern childGuard
    simpa only [d1354, d2232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1354, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12922 pattern childGuard
    simpa only [d1354, d2232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12924 (pattern : Twelve) (guard : d1865 pattern = 1) : d1649 pattern ≤ (1 : Int) + d2233 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1649, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12687 pattern childGuard
    simpa only [d1649, d2233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1649, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12893 pattern childGuard
    simpa only [d1649, d2233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12925 (pattern : Twelve) (guard : d1865 pattern = 1) : d1650 pattern ≤ (1 : Int) + d2234 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1650, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12736 pattern childGuard
    simpa only [d1650, d2234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1650, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1650, d2234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12926 (pattern : Twelve) (guard : d1865 pattern = 1) : d1656 pattern ≤ (1 : Int) + d2235 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1656, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12924 pattern childGuard
    simpa only [d1656, d2235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1656, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12925 pattern childGuard
    simpa only [d1656, d2235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12927 (pattern : Twelve) (guard : d1865 pattern = 1) : d1644 pattern ≤ (1 : Int) + d2236 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1644, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12893 pattern childGuard
    simpa only [d1644, d2236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1644, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12694 pattern childGuard
    simpa only [d1644, d2236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12928 (pattern : Twelve) (guard : d1865 pattern = 1) : d1645 pattern ≤ (1 : Int) + d2237 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1645, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12893 pattern childGuard
    simpa only [d1645, d2237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1645, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1645, d2237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12929 (pattern : Twelve) (guard : d1865 pattern = 1) : d1647 pattern ≤ (1 : Int) + d2238 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1647, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12927 pattern childGuard
    simpa only [d1647, d2238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1647, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12928 pattern childGuard
    simpa only [d1647, d2238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12930 (pattern : Twelve) (guard : d1865 pattern = 1) : d1651 pattern ≤ (1 : Int) + d2239 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1651, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12871 pattern childGuard
    simpa only [d1651, d2239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1651, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12929 pattern childGuard
    simpa only [d1651, d2239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12931 (pattern : Twelve) (guard : d1865 pattern = 1) : d1657 pattern ≤ (1 : Int) + d2240 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1657, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12930 pattern childGuard
    simpa only [d1657, d2240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1657, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12885 pattern childGuard
    simpa only [d1657, d2240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12932 (pattern : Twelve) (guard : d1865 pattern = 1) : d1660 pattern ≤ (1 : Int) + d2241 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1660, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12926 pattern childGuard
    simpa only [d1660, d2241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1660, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12931 pattern childGuard
    simpa only [d1660, d2241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12933 (pattern : Twelve) (guard : d1865 pattern = 1) : d1652 pattern ≤ (1 : Int) + d2242 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1652, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12790 pattern childGuard
    simpa only [d1652, d2242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1652, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12927 pattern childGuard
    simpa only [d1652, d2242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12934 (pattern : Twelve) (guard : d1865 pattern = 1) : d1653 pattern ≤ (1 : Int) + d2243 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1653, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12812 pattern childGuard
    simpa only [d1653, d2243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1653, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1653, d2243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12935 (pattern : Twelve) (guard : d1865 pattern = 1) : d1658 pattern ≤ (1 : Int) + d2244 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1658, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12933 pattern childGuard
    simpa only [d1658, d2244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1658, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12934 pattern childGuard
    simpa only [d1658, d2244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12936 (pattern : Twelve) (guard : d1865 pattern = 1) : d1646 pattern ≤ (1 : Int) + d2119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1646, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12694 pattern childGuard
    simpa only [d1646, d2119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1646, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d1646, d2119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12937 (pattern : Twelve) (guard : d1865 pattern = 1) : d1648 pattern ≤ (1 : Int) + d2119 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12936 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12776 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12938 (pattern : Twelve) (guard : d1865 pattern = 1) : d1654 pattern ≤ (1 : Int) + d2245 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1654, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12884 pattern childGuard
    simpa only [d1654, d2245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1654, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12937 pattern childGuard
    simpa only [d1654, d2245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12939 (pattern : Twelve) (guard : d1865 pattern = 1) : d1655 pattern ≤ (1 : Int) + d2246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1655, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12813 pattern childGuard
    simpa only [d1655, d2246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1655, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1655, d2246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12940 (pattern : Twelve) (guard : d1865 pattern = 1) : d1659 pattern ≤ (1 : Int) + d2247 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1659, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12938 pattern childGuard
    simpa only [d1659, d2247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1659, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12939 pattern childGuard
    simpa only [d1659, d2247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12941 (pattern : Twelve) (guard : d1865 pattern = 1) : d1661 pattern ≤ (1 : Int) + d2248 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1661, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12935 pattern childGuard
    simpa only [d1661, d2248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1661, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12940 pattern childGuard
    simpa only [d1661, d2248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12942 (pattern : Twelve) (guard : d1865 pattern = 1) : d1662 pattern ≤ (1 : Int) + d2249 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1662, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12931 pattern childGuard
    simpa only [d1662, d2249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1662, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1662, d2249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12943 (pattern : Twelve) (guard : d1865 pattern = 1) : d1663 pattern ≤ (1 : Int) + d2250 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1663, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12941 pattern childGuard
    simpa only [d1663, d2250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1663, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12942 pattern childGuard
    simpa only [d1663, d2250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12944 (pattern : Twelve) (guard : d1865 pattern = 1) : d1664 pattern ≤ (1 : Int) + d2251 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1664, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12932 pattern childGuard
    simpa only [d1664, d2251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1664, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12943 pattern childGuard
    simpa only [d1664, d2251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12945 (pattern : Twelve) (guard : d1865 pattern = 1) : d1668 pattern ≤ (1 : Int) + d2252 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1668, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12687 pattern childGuard
    simpa only [d1668, d2252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1668, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12927 pattern childGuard
    simpa only [d1668, d2252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12946 (pattern : Twelve) (guard : d1865 pattern = 1) : d1671 pattern ≤ (1 : Int) + d2253 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1671, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12945 pattern childGuard
    simpa only [d1671, d2253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1671, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12925 pattern childGuard
    simpa only [d1671, d2253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12947 (pattern : Twelve) (guard : d1865 pattern = 1) : d1674 pattern ≤ (1 : Int) + d2254 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1674, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12946 pattern childGuard
    simpa only [d1674, d2254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1674, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12931 pattern childGuard
    simpa only [d1674, d2254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12948 (pattern : Twelve) (guard : d1865 pattern = 1) : d1665 pattern ≤ (1 : Int) + d2237 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1665, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12893 pattern childGuard
    simpa only [d1665, d2237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1665, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d1665, d2237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12949 (pattern : Twelve) (guard : d1865 pattern = 1) : d1666 pattern ≤ (1 : Int) + d2238 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1666, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12927 pattern childGuard
    simpa only [d1666, d2238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1666, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12948 pattern childGuard
    simpa only [d1666, d2238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12950 (pattern : Twelve) (guard : d1865 pattern = 1) : d1669 pattern ≤ (1 : Int) + d2255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1669, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12790 pattern childGuard
    simpa only [d1669, d2255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1669, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12949 pattern childGuard
    simpa only [d1669, d2255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12951 (pattern : Twelve) (guard : d1865 pattern = 1) : d1672 pattern ≤ (1 : Int) + d2256 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12950 pattern childGuard
    simpa only [d1672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12885 pattern childGuard
    simpa only [d1672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12952 (pattern : Twelve) (guard : d1865 pattern = 1) : d1667 pattern ≤ (1 : Int) + d2257 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1667, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12776 pattern childGuard
    simpa only [d1667, d2257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1667, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12664 pattern childGuard
    simpa only [d1667, d2257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12953 (pattern : Twelve) (guard : d1865 pattern = 1) : d1670 pattern ≤ (1 : Int) + d2258 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1670, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12884 pattern childGuard
    simpa only [d1670, d2258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1670, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12952 pattern childGuard
    simpa only [d1670, d2258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12954 (pattern : Twelve) (guard : d1865 pattern = 1) : d1252 pattern ≤ (1 : Int) + d2259 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1252, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12813 pattern childGuard
    simpa only [d1252, d2259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1252, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1252, d2259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12955 (pattern : Twelve) (guard : d1865 pattern = 1) : d1626 pattern ≤ (1 : Int) + d2260 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1626, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12954 pattern childGuard
    simpa only [d1626, d2260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1626, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1626, d2260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12956 (pattern : Twelve) (guard : d1865 pattern = 1) : d1673 pattern ≤ (1 : Int) + d2261 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1673, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12953 pattern childGuard
    simpa only [d1673, d2261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1673, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12955 pattern childGuard
    simpa only [d1673, d2261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12957 (pattern : Twelve) (guard : d1865 pattern = 1) : d1675 pattern ≤ (1 : Int) + d2262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1675, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12951 pattern childGuard
    simpa only [d1675, d2262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1675, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12956 pattern childGuard
    simpa only [d1675, d2262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12958 (pattern : Twelve) (guard : d1865 pattern = 1) : d1676 pattern ≤ (1 : Int) + d2263 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1676, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12957 pattern childGuard
    simpa only [d1676, d2263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1676, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12942 pattern childGuard
    simpa only [d1676, d2263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12959 (pattern : Twelve) (guard : d1865 pattern = 1) : d1677 pattern ≤ (1 : Int) + d2264 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1677, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12947 pattern childGuard
    simpa only [d1677, d2264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1677, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12958 pattern childGuard
    simpa only [d1677, d2264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12960 (pattern : Twelve) (guard : d1865 pattern = 1) : d1678 pattern ≤ (1 : Int) + d2265 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1678, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12944 pattern childGuard
    simpa only [d1678, d2265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1678, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12959 pattern childGuard
    simpa only [d1678, d2265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12961 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (5 : Int) + d0 pattern := by
  omega
theorem c12962 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (5 : Int) + d1 pattern := by
  change (0 : Int) ≤ (5 : Int) + 1
  decide
theorem c12963 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (5 : Int) + d7 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12962 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12964 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (5 : Int) + d17 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12963 pattern childGuard
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12965 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (5 : Int) + d1 pattern := by
  omega
theorem c12966 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (5 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12965 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12967 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (5 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12962 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12965 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12968 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (5 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12963 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12967 pattern childGuard
    simpa only [d17, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12969 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (5 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12968 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12965 pattern childGuard
    simpa only [d27, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12970 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (5 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12966 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12969 pattern childGuard
    simpa only [d50, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12971 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (5 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12970 pattern childGuard
    simpa only [d72, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12972 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (5 : Int) + d2 pattern := by
  change (0 : Int) ≤ (5 : Int) + 2
  decide
theorem c12973 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (5 : Int) + d10 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12974 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (5 : Int) + d3 pattern := by
  change (1 : Int) ≤ (5 : Int) + 3
  decide
theorem c12975 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (5 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12962 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12976 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (5 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12973 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12975 pattern childGuard
    simpa only [d17, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12977 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (5 : Int) + d2 pattern := by
  change (1 : Int) ≤ (5 : Int) + 2
  decide
theorem c12978 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (5 : Int) + d4 pattern := by
  change (2 : Int) ≤ (5 : Int) + 4
  decide
theorem c12979 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (5 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12977 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12980 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (5 : Int) + d3 pattern := by
  change (2 : Int) ≤ (5 : Int) + 3
  decide
theorem c12981 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d5 pattern := by
  change (3 : Int) ≤ (5 : Int) + 5
  decide
theorem c12982 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (5 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d9, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12983 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (5 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12979 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12982 pattern childGuard
    simpa only [d18, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12984 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (5 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12976 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12983 pattern childGuard
    simpa only [d28, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12985 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (5 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d10, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12986 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (5 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d11, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12987 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (5 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12985 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12986 pattern childGuard
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12988 (pattern : Twelve) (guard : d1 pattern = 1) : d6 pattern ≤ (5 : Int) + d6 pattern := by
  omega
theorem c12989 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (5 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12987 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d29, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12990 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (5 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12984 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12989 pattern childGuard
    simpa only [d51, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12991 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (5 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12990 pattern childGuard
    simpa only [d73, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12992 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (5 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12971 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12991 pattern childGuard
    simpa only [d91, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12993 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (5 : Int) + d30 pattern := by
  omega
theorem c12994 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d6 pattern := by
  change (3 : Int) ≤ (5 : Int) + 6
  decide
theorem c12995 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (5 : Int) + d6 pattern := by
  change (5 : Int) ≤ (5 : Int) + 6
  decide
theorem c12996 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12994 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12995 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12997 (pattern : Twelve) (guard : d1 pattern = 1) : d4 pattern ≤ (5 : Int) + d6 pattern := by
  change (4 : Int) ≤ (5 : Int) + 6
  decide
theorem c12998 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12999 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12996 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12998 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13000 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (5 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12999 pattern childGuard
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13001 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (5 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12993 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13000 pattern childGuard
    simpa only [d52, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13002 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (5 : Int) + d2 pattern := by
  omega
theorem c13003 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (5 : Int) + d9 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13002 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12980 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13004 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (5 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13002 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13003 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13005 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (5 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13004 pattern childGuard
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13006 (pattern : Twelve) (guard : d1 pattern = 1) : d14 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12995 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13007 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12998 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13006 pattern childGuard
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13008 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (5 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12968 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d32, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13009 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (5 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13008 pattern childGuard
    simpa only [d53, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13010 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (5 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13001 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13009 pattern childGuard
    simpa only [d74, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13011 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13006 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13012 (pattern : Twelve) (guard : d1 pattern = 1) : d33 pattern ≤ (5 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12964 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13011 pattern childGuard
    simpa only [d33, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13013 (pattern : Twelve) (guard : d1 pattern = 1) : d54 pattern ≤ (5 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13005 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13012 pattern childGuard
    simpa only [d54, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13014 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (5 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13002 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13015 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (5 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13014 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12982 pattern childGuard
    simpa only [d23, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13016 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12976 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13015 pattern childGuard
    simpa only [d34, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13017 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (5 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13016 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12989 pattern childGuard
    simpa only [d55, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13018 (pattern : Twelve) (guard : d1 pattern = 1) : d75 pattern ≤ (5 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13013 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13017 pattern childGuard
    simpa only [d75, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13019 (pattern : Twelve) (guard : d1 pattern = 1) : d92 pattern ≤ (5 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13010 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13018 pattern childGuard
    simpa only [d92, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
