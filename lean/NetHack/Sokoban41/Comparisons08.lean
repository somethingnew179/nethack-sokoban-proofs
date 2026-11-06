/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons07
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c1280 (pattern : Ten) (guard : d394 pattern = 1) : d336 pattern ≤ (0 : Int) + d336 pattern := by
  omega
theorem c1281 (pattern : Ten) (guard : d394 pattern = 1) : d338 pattern ≤ (0 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d338, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1279 pattern childGuard
    simpa only [d338, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d338, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1280 pattern childGuard
    simpa only [d338, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1282 (pattern : Ten) (guard : d394 pattern = 1) : d213 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d394, d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1174 pattern childGuard
    simpa only [d394, d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1283 (pattern : Ten) (guard : d394 pattern = 1) : d337 pattern ≤ (0 : Int) + d337 pattern := by
  omega
theorem c1284 (pattern : Ten) (guard : d394 pattern = 1) : d339 pattern ≤ (0 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d339, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1282 pattern childGuard
    simpa only [d339, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d339, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1283 pattern childGuard
    simpa only [d339, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1285 (pattern : Ten) (guard : d394 pattern = 1) : d340 pattern ≤ (0 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d340, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1281 pattern childGuard
    simpa only [d340, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d340, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1284 pattern childGuard
    simpa only [d340, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1286 (pattern : Ten) (guard : d404 pattern = 1) : d332 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1219 pattern childGuard
    simpa only [d404, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1287 (pattern : Ten) (guard : d0 pattern = 1) : d336 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1288 (pattern : Ten) (guard : d405 pattern = 1) : d338 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d404 pattern = 1 := by simpa only [d405, d338, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1286 pattern childGuard
    simpa only [d405, d338, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d405, d338, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1287 pattern childGuard
    simpa only [d405, d338, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1289 (pattern : Ten) (guard : d404 pattern = 1) : d213 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d404, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1290 (pattern : Ten) (guard : d0 pattern = 1) : d337 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1291 (pattern : Ten) (guard : d405 pattern = 1) : d339 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d404 pattern = 1 := by simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1289 pattern childGuard
    simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1290 pattern childGuard
    simpa only [d405, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1292 (pattern : Ten) (guard : d405 pattern = 1) : d340 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d405 pattern = 1 := by simpa only [d340, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1288 pattern childGuard
    simpa only [d340, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d405 pattern = 1 := by simpa only [d340, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d340, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1293 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1294 (pattern : Ten) (guard : d395 pattern = 1) : d160 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d160, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d160, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d160, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1293 pattern childGuard
    simpa only [d395, d160, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1295 (pattern : Ten) (guard : d0 pattern = 1) : d159 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1296 (pattern : Ten) (guard : d395 pattern = 1) : d161 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1295 pattern childGuard
    simpa only [d395, d161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1297 (pattern : Ten) (guard : d395 pattern = 1) : d165 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1294 pattern childGuard
    simpa only [d165, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1296 pattern childGuard
    simpa only [d165, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1298 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1299 (pattern : Ten) (guard : d395 pattern = 1) : d162 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1298 pattern childGuard
    simpa only [d395, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1300 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d55 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1301 (pattern : Ten) (guard : d395 pattern = 1) : d163 pattern ≤ (0 : Int) + d55 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1001 pattern childGuard
    simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1300 pattern childGuard
    simpa only [d395, d163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1302 (pattern : Ten) (guard : d395 pattern = 1) : d166 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d166, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1299 pattern childGuard
    simpa only [d166, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d166, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1301 pattern childGuard
    simpa only [d166, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1303 (pattern : Ten) (guard : d395 pattern = 1) : d168 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d168, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1297 pattern childGuard
    simpa only [d168, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d168, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1302 pattern childGuard
    simpa only [d168, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1304 (pattern : Ten) (guard : d0 pattern = 1) : d57 pattern ≤ (0 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1305 (pattern : Ten) (guard : d395 pattern = 1) : d164 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1304 pattern childGuard
    simpa only [d395, d164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1306 (pattern : Ten) (guard : d395 pattern = 1) : d167 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1305 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1007 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1307 (pattern : Ten) (guard : d395 pattern = 1) : d169 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d169, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1306 pattern childGuard
    simpa only [d169, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d169, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1011 pattern childGuard
    simpa only [d169, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1308 (pattern : Ten) (guard : d395 pattern = 1) : d170 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d170, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1303 pattern childGuard
    simpa only [d170, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d170, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1307 pattern childGuard
    simpa only [d170, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1309 (pattern : Ten) (guard : d394 pattern = 1) : d344 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d344, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d344, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d344, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1167 pattern childGuard
    simpa only [d394, d344, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1310 (pattern : Ten) (guard : d0 pattern = 1) : d343 pattern ≤ (0 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1311 (pattern : Ten) (guard : d394 pattern = 1) : d345 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1310 pattern childGuard
    simpa only [d394, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1312 (pattern : Ten) (guard : d394 pattern = 1) : d346 pattern ≤ (0 : Int) + d326 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1309 pattern childGuard
    simpa only [d346, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1311 pattern childGuard
    simpa only [d346, d326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1313 (pattern : Ten) (guard : d394 pattern = 1) : d347 pattern ≤ (0 : Int) + d329 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d347, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d347, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d347, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1256 pattern childGuard
    simpa only [d347, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1314 (pattern : Ten) (guard : d394 pattern = 1) : d214 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c872 pattern childGuard
    simpa only [d394, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1315 (pattern : Ten) (guard : d394 pattern = 1) : d348 pattern ≤ (0 : Int) + d330 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d348, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1314 pattern childGuard
    simpa only [d348, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d348, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1261 pattern childGuard
    simpa only [d348, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1316 (pattern : Ten) (guard : d394 pattern = 1) : d349 pattern ≤ (0 : Int) + d331 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d349, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1313 pattern childGuard
    simpa only [d349, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d349, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1315 pattern childGuard
    simpa only [d349, d331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1317 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (0 : Int) + d170 pattern := by
  omega
theorem c1318 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (0 : Int) + d349 pattern := by
  omega
theorem c1319 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1320 (pattern : Ten) (guard : d395 pattern = 1) : d160 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1319 pattern childGuard
    simpa only [d395, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1321 (pattern : Ten) (guard : d395 pattern = 1) : d165 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1320 pattern childGuard
    simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1296 pattern childGuard
    simpa only [d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1322 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1323 (pattern : Ten) (guard : d395 pattern = 1) : d162 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d162, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d395, d162, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d162, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1322 pattern childGuard
    simpa only [d395, d162, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1324 (pattern : Ten) (guard : d395 pattern = 1) : d163 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d395, d163, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1001 pattern childGuard
    simpa only [d395, d163, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d395, d163, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1322 pattern childGuard
    simpa only [d395, d163, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1325 (pattern : Ten) (guard : d395 pattern = 1) : d166 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d166, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1323 pattern childGuard
    simpa only [d166, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d166, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1324 pattern childGuard
    simpa only [d166, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1326 (pattern : Ten) (guard : d395 pattern = 1) : d168 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d168, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1321 pattern childGuard
    simpa only [d168, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d168, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1325 pattern childGuard
    simpa only [d168, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1327 (pattern : Ten) (guard : d395 pattern = 1) : d169 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d169, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1306 pattern childGuard
    simpa only [d169, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d169, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1272 pattern childGuard
    simpa only [d169, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1328 (pattern : Ten) (guard : d395 pattern = 1) : d170 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1326 pattern childGuard
    simpa only [d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d395 pattern = 1 := by simpa only [d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1327 pattern childGuard
    simpa only [d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1329 (pattern : Ten) (guard : d0 pattern = 1) : d325 pattern ≤ (0 : Int) + d324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1330 (pattern : Ten) (guard : d394 pattern = 1) : d344 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d344, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d344, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d344, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1329 pattern childGuard
    simpa only [d394, d344, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1331 (pattern : Ten) (guard : d0 pattern = 1) : d343 pattern ≤ (0 : Int) + d324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1332 (pattern : Ten) (guard : d394 pattern = 1) : d345 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d345, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d394, d345, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d345, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1331 pattern childGuard
    simpa only [d394, d345, d332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1333 (pattern : Ten) (guard : d394 pattern = 1) : d346 pattern ≤ (0 : Int) + d332 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1330 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1332 pattern childGuard
    simpa only [d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1334 (pattern : Ten) (guard : d394 pattern = 1) : d347 pattern ≤ (0 : Int) + d338 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d347, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d347, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d347, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1280 pattern childGuard
    simpa only [d347, d338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1335 (pattern : Ten) (guard : d394 pattern = 1) : d214 pattern ≤ (0 : Int) + d213 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, d214, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d394, d214, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, d214, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1024 pattern childGuard
    simpa only [d394, d214, d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1336 (pattern : Ten) (guard : d394 pattern = 1) : d348 pattern ≤ (0 : Int) + d339 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d348, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1335 pattern childGuard
    simpa only [d348, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d348, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1283 pattern childGuard
    simpa only [d348, d339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1337 (pattern : Ten) (guard : d394 pattern = 1) : d349 pattern ≤ (0 : Int) + d340 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d349, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1334 pattern childGuard
    simpa only [d349, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d394 pattern = 1 := by simpa only [d349, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1336 pattern childGuard
    simpa only [d349, d340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1338 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (1 : Int) + d170 pattern := by
  omega
theorem c1339 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (1 : Int) + d349 pattern := by
  omega
theorem c1340 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (2 : Int) + d170 pattern := by
  omega
theorem c1341 (pattern : Ten) (guard : d1 pattern = 1) : d349 pattern ≤ (2 : Int) + d349 pattern := by
  omega
theorem c1342 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (14 : Int) + d0 pattern := by
  omega
theorem c1343 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (14 : Int) + d1 pattern := by
  change (0 : Int) ≤ (14 : Int) + 1
  decide
theorem c1344 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (14 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1342 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1343 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1345 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (14 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1346 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (14 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1344 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1345 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1347 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (14 : Int) + d2 pattern := by
  omega
theorem c1348 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (14 : Int) + d3 pattern := by
  change (2 : Int) ≤ (14 : Int) + 3
  decide
theorem c1349 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (14 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1347 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1348 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1350 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (14 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1351 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (14 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1349 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1350 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1352 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (14 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1346 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1351 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1353 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (14 : Int) + d4 pattern := by
  omega
theorem c1354 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (14 : Int) + d5 pattern := by
  change (4 : Int) ≤ (14 : Int) + 5
  decide
theorem c1355 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (14 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1353 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1356 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (14 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1357 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (14 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1355 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1358 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (14 : Int) + d10 pattern := by
  omega
theorem c1359 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (14 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1357 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1360 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (14 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1352 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1359 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1361 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (14 : Int) + d6 pattern := by
  omega
theorem c1362 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (14 : Int) + d7 pattern := by
  change (6 : Int) ≤ (14 : Int) + 7
  decide
theorem c1363 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (14 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1361 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1362 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1364 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (14 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1365 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (14 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1363 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1364 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1366 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (14 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1365 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1367 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (14 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1366 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1368 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (14 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1360 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1367 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1369 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (14 : Int) + d310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1370 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (14 : Int) + d314 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1349 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1369 pattern childGuard
    simpa only [d350, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1371 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (14 : Int) + d311 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1372 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (14 : Int) + d315 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1355 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1371 pattern childGuard
    simpa only [d350, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1373 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (14 : Int) + d320 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1370 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1372 pattern childGuard
    simpa only [d44, d320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1374 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (14 : Int) + d312 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1375 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (14 : Int) + d316 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1363 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1374 pattern childGuard
    simpa only [d350, d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1376 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (14 : Int) + d319 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1375 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d43, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1377 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (14 : Int) + d323 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1373 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1376 pattern childGuard
    simpa only [d50, d323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1378 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (14 : Int) + d8 pattern := by
  omega
theorem c1379 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (14 : Int) + d9 pattern := by
  change (8 : Int) ≤ (14 : Int) + 9
  decide
theorem c1380 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (14 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1378 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1379 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1381 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (14 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1382 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (14 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1380 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1381 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1383 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (14 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1382 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d45, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1384 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (14 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1383 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d51, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1385 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (14 : Int) + d325 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1377 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1384 pattern childGuard
    simpa only [d55, d325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1386 (pattern : Ten) (guard : d350 pattern = 1) : d160 pattern ≤ (14 : Int) + d344 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1368 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1385 pattern childGuard
    simpa only [d160, d344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1387 (pattern : Ten) (guard : d350 pattern = 1) : d157 pattern ≤ (14 : Int) + d341 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1372 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1375 pattern childGuard
    simpa only [d157, d341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1388 (pattern : Ten) (guard : d350 pattern = 1) : d158 pattern ≤ (14 : Int) + d342 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1387 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1383 pattern childGuard
    simpa only [d158, d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1389 (pattern : Ten) (guard : d350 pattern = 1) : d159 pattern ≤ (14 : Int) + d343 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1388 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d159, d343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1390 (pattern : Ten) (guard : d350 pattern = 1) : d161 pattern ≤ (14 : Int) + d345 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1368 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1389 pattern childGuard
    simpa only [d161, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1391 (pattern : Ten) (guard : d350 pattern = 1) : d165 pattern ≤ (14 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1386 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1390 pattern childGuard
    simpa only [d165, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1392 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (14 : Int) + d309 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1393 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (14 : Int) + d313 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1344 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1392 pattern childGuard
    simpa only [d350, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1394 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (14 : Int) + d317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1393 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1370 pattern childGuard
    simpa only [d15, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1395 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (14 : Int) + d318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1372 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d42, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1396 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (14 : Int) + d321 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1394 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1395 pattern childGuard
    simpa only [d48, d321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1397 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (14 : Int) + d322 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1376 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d49, d322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1398 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (14 : Int) + d324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1396 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1397 pattern childGuard
    simpa only [d54, d324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1399 (pattern : Ten) (guard : d350 pattern = 1) : d162 pattern ≤ (14 : Int) + d333 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1398 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d162, d333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1400 (pattern : Ten) (guard : d350 pattern = 1) : d163 pattern ≤ (14 : Int) + d334 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1385 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d163, d334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1401 (pattern : Ten) (guard : d350 pattern = 1) : d166 pattern ≤ (14 : Int) + d336 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1399 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1400 pattern childGuard
    simpa only [d166, d336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1402 (pattern : Ten) (guard : d350 pattern = 1) : d168 pattern ≤ (14 : Int) + d347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1391 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1401 pattern childGuard
    simpa only [d168, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1403 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (14 : Int) + d8 pattern := by
  change (7 : Int) ≤ (14 : Int) + 8
  decide
theorem c1404 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (14 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1403 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1378 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1405 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (14 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1404 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1379 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1406 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (14 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1407 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (14 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1406 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1408 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (14 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1407 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1409 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (14 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1408 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1410 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (14 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1409 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1411 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (14 : Int) + d10 pattern := by
  change (9 : Int) ≤ (14 : Int) + 10
  decide
theorem c1412 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (14 : Int) + d10 pattern := by
  omega
theorem c1413 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1411 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1414 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1413 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1412 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1415 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (14 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1416 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1414 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1417 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1416 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1418 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1417 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1419 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1420 (pattern : Ten) (guard : d350 pattern = 1) : d164 pattern ≤ (14 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1410 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1419 pattern childGuard
    simpa only [d164, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1421 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (14 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1410 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d60, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1422 (pattern : Ten) (guard : d350 pattern = 1) : d167 pattern ≤ (14 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1420 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1421 pattern childGuard
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1423 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (14 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1424 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (14 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1423 pattern childGuard
    simpa only [d350, d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1425 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (14 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1424 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d46, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1426 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (14 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1425 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d52, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1427 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (14 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1426 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d56, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1428 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (14 : Int) + d335 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1427 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d60, d335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1429 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1419 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1358 pattern childGuard
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1430 (pattern : Ten) (guard : d350 pattern = 1) : d63 pattern ≤ (14 : Int) + d337 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1428 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1429 pattern childGuard
    simpa only [d63, d337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1431 (pattern : Ten) (guard : d350 pattern = 1) : d169 pattern ≤ (14 : Int) + d348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1422 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1430 pattern childGuard
    simpa only [d169, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1432 (pattern : Ten) (guard : d350 pattern = 1) : d170 pattern ≤ (14 : Int) + d349 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1402 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1431 pattern childGuard
    simpa only [d170, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1433 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (14 : Int) + d10 pattern := by
  change (0 : Int) ≤ (14 : Int) + 10
  decide
theorem c1434 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (14 : Int) + d10 pattern := by
  change (1 : Int) ≤ (14 : Int) + 10
  decide
theorem c1435 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1433 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1434 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1436 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (14 : Int) + d10 pattern := by
  change (2 : Int) ≤ (14 : Int) + 10
  decide
theorem c1437 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (14 : Int) + d10 pattern := by
  change (3 : Int) ≤ (14 : Int) + 10
  decide
theorem c1438 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1436 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1437 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1439 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (14 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1435 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1438 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
