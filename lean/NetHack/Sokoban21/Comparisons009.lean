/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons008
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c1260 (pattern : Twelve) (guard : d1847 pattern = 1) : d1703 pattern ≤ (0 : Int) + d1712 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1703, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1258 pattern childGuard
    simpa only [d1703, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1703, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1259 pattern childGuard
    simpa only [d1703, d1712, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1261 (pattern : Twelve) (guard : d1847 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1713 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1704, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1254 pattern childGuard
    simpa only [d1704, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1847 pattern = 1 := by simpa only [d1704, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1260 pattern childGuard
    simpa only [d1704, d1713, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1262 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1263 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1262 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1264 (pattern : Twelve) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1265 (pattern : Twelve) (guard : d1849 pattern = 1) : d235 pattern ≤ (0 : Int) + d184 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d235, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1263 pattern childGuard
    simpa only [d1849, d235, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d235, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1264 pattern childGuard
    simpa only [d1849, d235, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1266 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d161 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1267 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1266 pattern childGuard
    simpa only [d1848, d26, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1268 (pattern : Twelve) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d366 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1269 (pattern : Twelve) (guard : d1849 pattern = 1) : d236 pattern ≤ (0 : Int) + d372 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d236, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d1849, d236, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d236, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1268 pattern childGuard
    simpa only [d1849, d236, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1270 (pattern : Twelve) (guard : d1849 pattern = 1) : d256 pattern ≤ (0 : Int) + d389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d256, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1265 pattern childGuard
    simpa only [d256, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d256, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1269 pattern childGuard
    simpa only [d256, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1271 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d161 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1272 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1271 pattern childGuard
    simpa only [d1848, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1273 (pattern : Twelve) (guard : d0 pattern = 1) : d172 pattern ≤ (0 : Int) + d367 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1274 (pattern : Twelve) (guard : d1849 pattern = 1) : d237 pattern ≤ (0 : Int) + d373 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d237, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1272 pattern childGuard
    simpa only [d1849, d237, d373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d237, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1273 pattern childGuard
    simpa only [d1849, d237, d373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1275 (pattern : Twelve) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d163 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1276 (pattern : Twelve) (guard : d1848 pattern = 1) : d28 pattern ≤ (0 : Int) + d366 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d28, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d28, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d28, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1275 pattern childGuard
    simpa only [d1848, d28, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1277 (pattern : Twelve) (guard : d1849 pattern = 1) : d238 pattern ≤ (0 : Int) + d374 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d238, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1276 pattern childGuard
    simpa only [d1849, d238, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d238, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c817 pattern childGuard
    simpa only [d1849, d238, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1278 (pattern : Twelve) (guard : d1849 pattern = 1) : d257 pattern ≤ (0 : Int) + d390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d257, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1274 pattern childGuard
    simpa only [d257, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d257, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1277 pattern childGuard
    simpa only [d257, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1279 (pattern : Twelve) (guard : d1849 pattern = 1) : d272 pattern ≤ (0 : Int) + d402 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d272, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1270 pattern childGuard
    simpa only [d272, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d272, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1278 pattern childGuard
    simpa only [d272, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1280 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d165 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1281 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d368 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1280 pattern childGuard
    simpa only [d1848, d30, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1282 (pattern : Twelve) (guard : d0 pattern = 1) : d175 pattern ≤ (0 : Int) + d369 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1283 (pattern : Twelve) (guard : d1849 pattern = 1) : d239 pattern ≤ (0 : Int) + d375 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d239, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1281 pattern childGuard
    simpa only [d1849, d239, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d239, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1282 pattern childGuard
    simpa only [d1849, d239, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1284 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d167 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1285 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d369 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1284 pattern childGuard
    simpa only [d1848, d30, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1286 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1287 (pattern : Twelve) (guard : d1849 pattern = 1) : d240 pattern ≤ (0 : Int) + d376 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d240, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1285 pattern childGuard
    simpa only [d1849, d240, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d240, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1286 pattern childGuard
    simpa only [d1849, d240, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1288 (pattern : Twelve) (guard : d1849 pattern = 1) : d258 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d258, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1283 pattern childGuard
    simpa only [d258, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d258, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1287 pattern childGuard
    simpa only [d258, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1289 (pattern : Twelve) (guard : d1849 pattern = 1) : d240 pattern ≤ (0 : Int) + d377 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d240, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1285 pattern childGuard
    simpa only [d1849, d240, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d240, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c968 pattern childGuard
    simpa only [d1849, d240, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1290 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1291 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1290 pattern childGuard
    simpa only [d1848, d34, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1292 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d378 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d1849, d241, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d241, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1293 (pattern : Twelve) (guard : d1849 pattern = 1) : d259 pattern ≤ (0 : Int) + d392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d259, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1289 pattern childGuard
    simpa only [d259, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d259, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1292 pattern childGuard
    simpa only [d259, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1294 (pattern : Twelve) (guard : d1849 pattern = 1) : d273 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d273, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1288 pattern childGuard
    simpa only [d273, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d273, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1293 pattern childGuard
    simpa only [d273, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1295 (pattern : Twelve) (guard : d1849 pattern = 1) : d284 pattern ≤ (0 : Int) + d409 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d284, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1279 pattern childGuard
    simpa only [d284, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d284, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1294 pattern childGuard
    simpa only [d284, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1296 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d165 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1297 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d368 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1296 pattern childGuard
    simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1298 (pattern : Twelve) (guard : d1849 pattern = 1) : d242 pattern ≤ (0 : Int) + d375 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1297 pattern childGuard
    simpa only [d1849, d242, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1282 pattern childGuard
    simpa only [d1849, d242, d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1299 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d167 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1300 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d369 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1299 pattern childGuard
    simpa only [d1848, d26, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1301 (pattern : Twelve) (guard : d1849 pattern = 1) : d243 pattern ≤ (0 : Int) + d376 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d243, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1300 pattern childGuard
    simpa only [d1849, d243, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d243, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1286 pattern childGuard
    simpa only [d1849, d243, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1302 (pattern : Twelve) (guard : d1849 pattern = 1) : d260 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d260, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1298 pattern childGuard
    simpa only [d260, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d260, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1301 pattern childGuard
    simpa only [d260, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1303 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d167 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1304 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d369 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1303 pattern childGuard
    simpa only [d1848, d369, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1305 (pattern : Twelve) (guard : d1849 pattern = 1) : d244 pattern ≤ (0 : Int) + d377 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d244, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1304 pattern childGuard
    simpa only [d1849, d244, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d244, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c968 pattern childGuard
    simpa only [d1849, d244, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1306 (pattern : Twelve) (guard : d1849 pattern = 1) : d261 pattern ≤ (0 : Int) + d392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d261, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1305 pattern childGuard
    simpa only [d261, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d261, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1292 pattern childGuard
    simpa only [d261, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1307 (pattern : Twelve) (guard : d1849 pattern = 1) : d274 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d274, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1302 pattern childGuard
    simpa only [d274, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d274, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1306 pattern childGuard
    simpa only [d274, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1308 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1309 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1308 pattern childGuard
    simpa only [d1848, d30, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1310 (pattern : Twelve) (guard : d1849 pattern = 1) : d245 pattern ≤ (0 : Int) + d379 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d245, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1309 pattern childGuard
    simpa only [d1849, d245, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d245, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c842 pattern childGuard
    simpa only [d1849, d245, d379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1311 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1312 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d1848, d30, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1313 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d246, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1849, d246, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1314 (pattern : Twelve) (guard : d1849 pattern = 1) : d262 pattern ≤ (0 : Int) + d393 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d262, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1310 pattern childGuard
    simpa only [d262, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d262, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1313 pattern childGuard
    simpa only [d262, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1315 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c847 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1316 (pattern : Twelve) (guard : d1849 pattern = 1) : d263 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1315 pattern childGuard
    simpa only [d263, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d263, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1292 pattern childGuard
    simpa only [d263, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1317 (pattern : Twelve) (guard : d1849 pattern = 1) : d275 pattern ≤ (0 : Int) + d404 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d275, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1314 pattern childGuard
    simpa only [d275, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d275, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1316 pattern childGuard
    simpa only [d275, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1318 (pattern : Twelve) (guard : d1849 pattern = 1) : d285 pattern ≤ (0 : Int) + d410 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d285, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1307 pattern childGuard
    simpa only [d285, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d285, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1317 pattern childGuard
    simpa only [d285, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1319 (pattern : Twelve) (guard : d1849 pattern = 1) : d293 pattern ≤ (0 : Int) + d415 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d293, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1295 pattern childGuard
    simpa only [d293, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d293, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1318 pattern childGuard
    simpa only [d293, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1320 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d169 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1321 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d370 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1320 pattern childGuard
    simpa only [d1848, d30, d370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1322 (pattern : Twelve) (guard : d0 pattern = 1) : d180 pattern ≤ (0 : Int) + d371 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1323 (pattern : Twelve) (guard : d1849 pattern = 1) : d247 pattern ≤ (0 : Int) + d381 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d247, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1321 pattern childGuard
    simpa only [d1849, d247, d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d247, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1322 pattern childGuard
    simpa only [d1849, d247, d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1324 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d170 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1325 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d371 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1324 pattern childGuard
    simpa only [d1848, d30, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1326 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1327 (pattern : Twelve) (guard : d1849 pattern = 1) : d248 pattern ≤ (0 : Int) + d382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d248, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1325 pattern childGuard
    simpa only [d1849, d248, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d248, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1326 pattern childGuard
    simpa only [d1849, d248, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1328 (pattern : Twelve) (guard : d1849 pattern = 1) : d264 pattern ≤ (0 : Int) + d395 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d264, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1323 pattern childGuard
    simpa only [d264, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d264, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1327 pattern childGuard
    simpa only [d264, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1329 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d35 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1330 (pattern : Twelve) (guard : d1849 pattern = 1) : d248 pattern ≤ (0 : Int) + d383 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d248, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1325 pattern childGuard
    simpa only [d1849, d248, d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d248, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1329 pattern childGuard
    simpa only [d1849, d248, d383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1331 (pattern : Twelve) (guard : d1849 pattern = 1) : d265 pattern ≤ (0 : Int) + d396 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1330 pattern childGuard
    simpa only [d265, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d265, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1292 pattern childGuard
    simpa only [d265, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1332 (pattern : Twelve) (guard : d1849 pattern = 1) : d276 pattern ≤ (0 : Int) + d405 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d276, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1328 pattern childGuard
    simpa only [d276, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d276, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1331 pattern childGuard
    simpa only [d276, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1333 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d2 pattern := by
  omega
theorem c1334 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1335 (pattern : Twelve) (guard : d1848 pattern = 1) : d38 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d1848, d38, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1336 (pattern : Twelve) (guard : d1849 pattern = 1) : d249 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c862 pattern childGuard
    simpa only [d1849, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1337 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d250, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d250, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d250, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d1849, d250, d384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1338 (pattern : Twelve) (guard : d1849 pattern = 1) : d266 pattern ≤ (0 : Int) + d397 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d266, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1336 pattern childGuard
    simpa only [d266, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d266, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1337 pattern childGuard
    simpa only [d266, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1339 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c867 pattern childGuard
    simpa only [d1849, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1340 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (0 : Int) + d23 pattern := by
  omega
theorem c1341 (pattern : Twelve) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1342 (pattern : Twelve) (guard : d1848 pattern = 1) : d41 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1341 pattern childGuard
    simpa only [d1848, d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1343 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d385 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d251, d385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1849, d251, d385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1344 (pattern : Twelve) (guard : d1849 pattern = 1) : d267 pattern ≤ (0 : Int) + d398 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1339 pattern childGuard
    simpa only [d267, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1343 pattern childGuard
    simpa only [d267, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1345 (pattern : Twelve) (guard : d1849 pattern = 1) : d277 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d277, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1338 pattern childGuard
    simpa only [d277, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d277, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1344 pattern childGuard
    simpa only [d277, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1346 (pattern : Twelve) (guard : d1849 pattern = 1) : d286 pattern ≤ (0 : Int) + d411 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d286, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1332 pattern childGuard
    simpa only [d286, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d286, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1345 pattern childGuard
    simpa only [d286, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1347 (pattern : Twelve) (guard : d1849 pattern = 1) : d252 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c874 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1348 (pattern : Twelve) (guard : d1849 pattern = 1) : d268 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d268, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1347 pattern childGuard
    simpa only [d268, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d268, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1313 pattern childGuard
    simpa only [d268, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1349 (pattern : Twelve) (guard : d1849 pattern = 1) : d278 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d278, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1348 pattern childGuard
    simpa only [d278, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d278, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1316 pattern childGuard
    simpa only [d278, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1350 (pattern : Twelve) (guard : d1849 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c1351 (pattern : Twelve) (guard : d1849 pattern = 1) : d287 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d287, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1349 pattern childGuard
    simpa only [d287, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d287, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d287, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1352 (pattern : Twelve) (guard : d1849 pattern = 1) : d294 pattern ≤ (0 : Int) + d416 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d294, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1346 pattern childGuard
    simpa only [d294, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d294, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1351 pattern childGuard
    simpa only [d294, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1353 (pattern : Twelve) (guard : d1849 pattern = 1) : d297 pattern ≤ (0 : Int) + d419 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d297, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1319 pattern childGuard
    simpa only [d297, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d297, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1352 pattern childGuard
    simpa only [d297, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1354 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d1848, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1355 (pattern : Twelve) (guard : d1849 pattern = 1) : d253 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c847 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1356 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1357 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d1848, d26, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1358 (pattern : Twelve) (guard : d1849 pattern = 1) : d254 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d254, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1357 pattern childGuard
    simpa only [d1849, d254, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d254, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1849, d254, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1359 (pattern : Twelve) (guard : d1849 pattern = 1) : d269 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1355 pattern childGuard
    simpa only [d269, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d269, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d269, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1360 (pattern : Twelve) (guard : d1849 pattern = 1) : d279 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d279, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1359 pattern childGuard
    simpa only [d279, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d279, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1316 pattern childGuard
    simpa only [d279, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1361 (pattern : Twelve) (guard : d1849 pattern = 1) : d246 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1315 pattern childGuard
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1313 pattern childGuard
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1362 (pattern : Twelve) (guard : d1849 pattern = 1) : d280 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1361 pattern childGuard
    simpa only [d280, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d280, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1316 pattern childGuard
    simpa only [d280, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1363 (pattern : Twelve) (guard : d1849 pattern = 1) : d288 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1360 pattern childGuard
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1362 pattern childGuard
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1364 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d397 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1339 pattern childGuard
    simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1337 pattern childGuard
    simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1365 (pattern : Twelve) (guard : d1849 pattern = 1) : d281 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1364 pattern childGuard
    simpa only [d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1344 pattern childGuard
    simpa only [d281, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1366 (pattern : Twelve) (guard : d1849 pattern = 1) : d289 pattern ≤ (0 : Int) + d413 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d289, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1362 pattern childGuard
    simpa only [d289, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d289, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1365 pattern childGuard
    simpa only [d289, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1367 (pattern : Twelve) (guard : d1849 pattern = 1) : d290 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d290, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1362 pattern childGuard
    simpa only [d290, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d290, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d290, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1368 (pattern : Twelve) (guard : d1849 pattern = 1) : d295 pattern ≤ (0 : Int) + d417 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d295, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1366 pattern childGuard
    simpa only [d295, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d295, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1367 pattern childGuard
    simpa only [d295, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1369 (pattern : Twelve) (guard : d1849 pattern = 1) : d298 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d298, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1363 pattern childGuard
    simpa only [d298, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d298, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1368 pattern childGuard
    simpa only [d298, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1370 (pattern : Twelve) (guard : d1849 pattern = 1) : d300 pattern ≤ (0 : Int) + d422 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d300, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1353 pattern childGuard
    simpa only [d300, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d300, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1369 pattern childGuard
    simpa only [d300, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1371 (pattern : Twelve) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1372 (pattern : Twelve) (guard : d1848 pattern = 1) : d28 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d28, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d28, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d28, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1371 pattern childGuard
    simpa only [d1848, d28, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1373 (pattern : Twelve) (guard : d1849 pattern = 1) : d255 pattern ≤ (0 : Int) + d378 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d255, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1372 pattern childGuard
    simpa only [d1849, d255, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d255, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d255, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1374 (pattern : Twelve) (guard : d1849 pattern = 1) : d270 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d270, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1355 pattern childGuard
    simpa only [d270, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d270, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1373 pattern childGuard
    simpa only [d270, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1375 (pattern : Twelve) (guard : d1849 pattern = 1) : d282 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d282, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1359 pattern childGuard
    simpa only [d282, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d282, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1374 pattern childGuard
    simpa only [d282, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1376 (pattern : Twelve) (guard : d1849 pattern = 1) : d291 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1375 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1362 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1377 (pattern : Twelve) (guard : d1849 pattern = 1) : d271 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d271, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1355 pattern childGuard
    simpa only [d271, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d271, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1292 pattern childGuard
    simpa only [d271, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1378 (pattern : Twelve) (guard : d1849 pattern = 1) : d283 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d283, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1359 pattern childGuard
    simpa only [d283, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d283, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1377 pattern childGuard
    simpa only [d283, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1379 (pattern : Twelve) (guard : d1849 pattern = 1) : d292 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1378 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1362 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1380 (pattern : Twelve) (guard : d1849 pattern = 1) : d296 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1376 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1379 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1381 (pattern : Twelve) (guard : d1849 pattern = 1) : d299 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d299, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1380 pattern childGuard
    simpa only [d299, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d299, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1368 pattern childGuard
    simpa only [d299, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1382 (pattern : Twelve) (guard : d1849 pattern = 1) : d301 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1381 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1369 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1383 (pattern : Twelve) (guard : d1849 pattern = 1) : d302 pattern ≤ (0 : Int) + d423 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d302, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1370 pattern childGuard
    simpa only [d302, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d302, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1382 pattern childGuard
    simpa only [d302, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1384 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d386 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d250, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d250, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d250, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1068 pattern childGuard
    simpa only [d1849, d250, d386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1385 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d400 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1339 pattern childGuard
    simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1384 pattern childGuard
    simpa only [d400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1386 (pattern : Twelve) (guard : d1849 pattern = 1) : d250 pattern ≤ (0 : Int) + d387 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d250, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d1849, d250, d387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d250, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c916 pattern childGuard
    simpa only [d1849, d250, d387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1387 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d388 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d1849, d251, d388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1121 pattern childGuard
    simpa only [d1849, d251, d388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1388 (pattern : Twelve) (guard : d1849 pattern = 1) : d267 pattern ≤ (0 : Int) + d401 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1386 pattern childGuard
    simpa only [d267, d401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d267, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1387 pattern childGuard
    simpa only [d267, d401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1389 (pattern : Twelve) (guard : d1849 pattern = 1) : d281 pattern ≤ (0 : Int) + d408 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d281, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1385 pattern childGuard
    simpa only [d281, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d281, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1388 pattern childGuard
    simpa only [d281, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1390 (pattern : Twelve) (guard : d1849 pattern = 1) : d289 pattern ≤ (0 : Int) + d414 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d289, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1362 pattern childGuard
    simpa only [d289, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d289, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1389 pattern childGuard
    simpa only [d289, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1391 (pattern : Twelve) (guard : d1849 pattern = 1) : d295 pattern ≤ (0 : Int) + d418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d295, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1390 pattern childGuard
    simpa only [d295, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d295, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1367 pattern childGuard
    simpa only [d295, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1392 (pattern : Twelve) (guard : d1849 pattern = 1) : d299 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d299, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1380 pattern childGuard
    simpa only [d299, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d299, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1391 pattern childGuard
    simpa only [d299, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1393 (pattern : Twelve) (guard : d1849 pattern = 1) : d298 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d298, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1363 pattern childGuard
    simpa only [d298, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d298, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1391 pattern childGuard
    simpa only [d298, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1394 (pattern : Twelve) (guard : d1849 pattern = 1) : d301 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1392 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1393 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1395 (pattern : Twelve) (guard : d1849 pattern = 1) : d303 pattern ≤ (0 : Int) + d424 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d303, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1383 pattern childGuard
    simpa only [d303, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d303, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1394 pattern childGuard
    simpa only [d303, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1396 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d163 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1397 (pattern : Twelve) (guard : d1848 pattern = 1) : d27 pattern ≤ (0 : Int) + d366 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d27, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d27, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d27, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1396 pattern childGuard
    simpa only [d1848, d27, d366, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1398 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1399 (pattern : Twelve) (guard : d1849 pattern = 1) : d940 pattern ≤ (0 : Int) + d1030 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d940, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1397 pattern childGuard
    simpa only [d1849, d940, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d940, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1398 pattern childGuard
    simpa only [d1849, d940, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
