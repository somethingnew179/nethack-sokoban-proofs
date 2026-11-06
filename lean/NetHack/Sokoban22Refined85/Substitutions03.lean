/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub360 (p : Pattern) : d97 (change p 49 (some 71)) = d97 p := by
  change (if p 138 then d96 (change p 49 (some 71)) else d87 (change p 49 (some 71))) = d97 p
  rw [sub359, sub350]
  rfl
theorem sub361 (p : Pattern) : d98 (change p 49 (some 71)) = d98 p := by
  change (if p 116 then d97 (change p 49 (some 71)) else d88 (change p 49 (some 71))) = d98 p
  rw [sub360, sub351]
  rfl
theorem sub362 (p : Pattern) : d99 (change p 49 (some 71)) = d99 p := by
  change (if p 138 then d12 (change p 49 (some 71)) else d87 (change p 49 (some 71))) = d99 p
  rw [sub269, sub350]
  rfl
theorem sub363 (p : Pattern) : d100 (change p 49 (some 71)) = d100 p := by
  change (if p 116 then d99 (change p 49 (some 71)) else d88 (change p 49 (some 71))) = d100 p
  rw [sub362, sub351]
  rfl
theorem sub364 (p : Pattern) : d101 (change p 49 (some 71)) = d101 p := by
  change (if p 115 then d100 (change p 49 (some 71)) else d98 (change p 49 (some 71))) = d101 p
  rw [sub363, sub361]
  rfl
theorem sub365 (p : Pattern) : d482 (change p 49 (some 71)) = d101 p := by
  change d101 (change p 49 (some 71)) = d101 p
  exact sub364 p
theorem sub366 (p : Pattern) : d483 (change p 49 (some 71)) = d101 p := by
  change d101 (change p 49 (some 71)) = d101 p
  exact sub364 p
theorem sub367 (p : Pattern) : d484 (change p 49 (some 71)) = d101 p := by
  change (if p 48 then d483 (change p 49 (some 71)) else d482 (change p 49 (some 71))) = d101 p
  rw [sub366, sub365]
  simp only [ite_self]
theorem sub368 (p : Pattern) : d268 (change p 10000 none) = d268 p := by
  change (if p 204 then d116 (change p 10000 none) else d103 (change p 10000 none)) = d268 p
  rw [sub114, sub99]
  rfl
theorem sub369 (p : Pattern) : d269 (change p 10000 none) = d269 p := by
  change (if p 182 then d117 (change p 10000 none) else d268 (change p 10000 none)) = d269 p
  rw [sub115, sub368]
  rfl
theorem sub370 (p : Pattern) : d270 (change p 10000 none) = d270 p := by
  change (if p 182 then d121 (change p 10000 none) else d268 (change p 10000 none)) = d270 p
  rw [sub120, sub368]
  rfl
theorem sub371 (p : Pattern) : d271 (change p 10000 none) = d271 p := by
  change (if p 163 then d270 (change p 10000 none) else d269 (change p 10000 none)) = d271 p
  rw [sub370, sub369]
  rfl
theorem sub372 (p : Pattern) : d272 (change p 10000 none) = d272 p := by
  change (if p 182 then d12 (change p 10000 none) else d268 (change p 10000 none)) = d272 p
  rw [sub1, sub368]
  rfl
theorem sub373 (p : Pattern) : d273 (change p 10000 none) = d273 p := by
  change (if p 204 then d120 (change p 10000 none) else d107 (change p 10000 none)) = d273 p
  rw [sub119, sub104]
  rfl
theorem sub374 (p : Pattern) : d274 (change p 10000 none) = d274 p := by
  change (if p 182 then d12 (change p 10000 none) else d273 (change p 10000 none)) = d274 p
  rw [sub1, sub373]
  rfl
theorem sub375 (p : Pattern) : d275 (change p 10000 none) = d275 p := by
  change (if p 163 then d274 (change p 10000 none) else d272 (change p 10000 none)) = d275 p
  rw [sub374, sub372]
  rfl
theorem sub376 (p : Pattern) : d276 (change p 10000 none) = d276 p := by
  change (if p 162 then d275 (change p 10000 none) else d271 (change p 10000 none)) = d276 p
  rw [sub375, sub371]
  rfl
theorem sub377 (p : Pattern) : d277 (change p 10000 none) = d277 p := by
  change (if p 182 then d12 (change p 10000 none) else d59 (change p 10000 none)) = d277 p
  rw [sub1, sub54]
  rfl
theorem sub378 (p : Pattern) : d278 (change p 10000 none) = d278 p := by
  change (if p 163 then d12 (change p 10000 none) else d277 (change p 10000 none)) = d278 p
  rw [sub1, sub377]
  rfl
theorem sub379 (p : Pattern) : d279 (change p 10000 none) = d279 p := by
  change (if p 162 then d278 (change p 10000 none) else d275 (change p 10000 none)) = d279 p
  rw [sub378, sub375]
  rfl
theorem sub380 (p : Pattern) : d280 (change p 10000 none) = d280 p := by
  change (if p 161 then d279 (change p 10000 none) else d276 (change p 10000 none)) = d280 p
  rw [sub379, sub376]
  rfl
theorem sub381 (p : Pattern) : d281 (change p 10000 none) = d281 p := by
  change (if p 160 then d280 (change p 10000 none) else d114 (change p 10000 none)) = d281 p
  rw [sub380, sub111]
  rfl
theorem sub382 (p : Pattern) : d282 (change p 10000 none) = d282 p := by
  change (if p 204 then d107 (change p 10000 none) else d116 (change p 10000 none)) = d282 p
  rw [sub104, sub114]
  rfl
theorem sub383 (p : Pattern) : d283 (change p 10000 none) = d283 p := by
  change (if p 182 then d12 (change p 10000 none) else d282 (change p 10000 none)) = d283 p
  rw [sub1, sub382]
  rfl
theorem sub384 (p : Pattern) : d284 (change p 10000 none) = d284 p := by
  change (if p 163 then d283 (change p 10000 none) else d270 (change p 10000 none)) = d284 p
  rw [sub383, sub370]
  rfl
theorem sub385 (p : Pattern) : d285 (change p 10000 none) = d285 p := by
  change (if p 163 then d12 (change p 10000 none) else d274 (change p 10000 none)) = d285 p
  rw [sub1, sub374]
  rfl
theorem sub386 (p : Pattern) : d286 (change p 10000 none) = d286 p := by
  change (if p 162 then d285 (change p 10000 none) else d284 (change p 10000 none)) = d286 p
  rw [sub385, sub384]
  rfl
theorem sub387 (p : Pattern) : d287 (change p 10000 none) = d287 p := by
  change (if p 162 then d12 (change p 10000 none) else d285 (change p 10000 none)) = d287 p
  rw [sub1, sub385]
  rfl
theorem sub388 (p : Pattern) : d288 (change p 10000 none) = d288 p := by
  change (if p 161 then d287 (change p 10000 none) else d286 (change p 10000 none)) = d288 p
  rw [sub387, sub386]
  rfl
theorem sub389 (p : Pattern) : d289 (change p 10000 none) = d289 p := by
  change (if p 160 then d288 (change p 10000 none) else d214 (change p 10000 none)) = d289 p
  rw [sub388, sub214]
  rfl
theorem sub390 (p : Pattern) : d290 (change p 10000 none) = d290 p := by
  change (if p 141 then d289 (change p 10000 none) else d281 (change p 10000 none)) = d290 p
  rw [sub389, sub381]
  rfl
theorem sub391 (p : Pattern) : d291 (change p 10000 none) = d291 p := by
  change (if p 163 then d269 (change p 10000 none) else d105 (change p 10000 none)) = d291 p
  rw [sub369, sub101]
  rfl
theorem sub392 (p : Pattern) : d292 (change p 10000 none) = d292 p := by
  change (if p 182 then d121 (change p 10000 none) else d273 (change p 10000 none)) = d292 p
  rw [sub120, sub373]
  rfl
theorem sub393 (p : Pattern) : d293 (change p 10000 none) = d293 p := by
  change (if p 163 then d292 (change p 10000 none) else d269 (change p 10000 none)) = d293 p
  rw [sub392, sub369]
  rfl
theorem sub394 (p : Pattern) : d294 (change p 10000 none) = d294 p := by
  change (if p 162 then d293 (change p 10000 none) else d291 (change p 10000 none)) = d294 p
  rw [sub393, sub391]
  rfl
theorem sub395 (p : Pattern) : d295 (change p 10000 none) = d295 p := by
  change (if p 162 then d278 (change p 10000 none) else d293 (change p 10000 none)) = d295 p
  rw [sub378, sub393]
  rfl
theorem sub396 (p : Pattern) : d296 (change p 10000 none) = d296 p := by
  change (if p 161 then d295 (change p 10000 none) else d294 (change p 10000 none)) = d296 p
  rw [sub395, sub394]
  rfl
theorem sub397 (p : Pattern) : d297 (change p 10000 none) = d297 p := by
  change (if p 160 then d151 (change p 10000 none) else d296 (change p 10000 none)) = d297 p
  rw [sub150, sub396]
  rfl
theorem sub398 (p : Pattern) : d298 (change p 10000 none) = d298 p := by
  change (if p 182 then d108 (change p 10000 none) else d282 (change p 10000 none)) = d298 p
  rw [sub105, sub382]
  rfl
theorem sub399 (p : Pattern) : d299 (change p 10000 none) = d299 p := by
  change (if p 163 then d298 (change p 10000 none) else d269 (change p 10000 none)) = d299 p
  rw [sub398, sub369]
  rfl
theorem sub400 (p : Pattern) : d300 (change p 10000 none) = d300 p := by
  change (if p 163 then d12 (change p 10000 none) else d292 (change p 10000 none)) = d300 p
  rw [sub1, sub392]
  rfl
theorem sub401 (p : Pattern) : d301 (change p 10000 none) = d301 p := by
  change (if p 162 then d300 (change p 10000 none) else d299 (change p 10000 none)) = d301 p
  rw [sub400, sub399]
  rfl
theorem sub402 (p : Pattern) : d302 (change p 10000 none) = d302 p := by
  change (if p 162 then d12 (change p 10000 none) else d300 (change p 10000 none)) = d302 p
  rw [sub1, sub400]
  rfl
theorem sub403 (p : Pattern) : d303 (change p 10000 none) = d303 p := by
  change (if p 161 then d302 (change p 10000 none) else d301 (change p 10000 none)) = d303 p
  rw [sub402, sub401]
  rfl
theorem sub404 (p : Pattern) : d304 (change p 10000 none) = d304 p := by
  change (if p 160 then d155 (change p 10000 none) else d303 (change p 10000 none)) = d304 p
  rw [sub154, sub403]
  rfl
theorem sub405 (p : Pattern) : d305 (change p 10000 none) = d305 p := by
  change (if p 141 then d304 (change p 10000 none) else d297 (change p 10000 none)) = d305 p
  rw [sub404, sub397]
  rfl
theorem sub406 (p : Pattern) : d306 (change p 10000 none) = d306 p := by
  change (if p 138 then d305 (change p 10000 none) else d290 (change p 10000 none)) = d306 p
  rw [sub405, sub390]
  rfl
theorem sub407 (p : Pattern) : d307 (change p 10000 none) = d307 p := by
  change (if p 138 then d12 (change p 10000 none) else d305 (change p 10000 none)) = d307 p
  rw [sub1, sub405]
  rfl
theorem sub408 (p : Pattern) : d308 (change p 10000 none) = d308 p := by
  change (if p 116 then d307 (change p 10000 none) else d306 (change p 10000 none)) = d308 p
  rw [sub407, sub406]
  rfl
theorem sub409 (p : Pattern) : d309 (change p 10000 none) = d309 p := by
  change (if p 115 then d308 (change p 10000 none) else d225 (change p 10000 none)) = d309 p
  rw [sub408, sub225]
  rfl
theorem sub410 (p : Pattern) : d310 (change p 10000 none) = d310 p := by
  change (if p 71 then d309 (change p 10000 none) else d101 (change p 10000 none)) = d310 p
  rw [sub409, sub96]
  rfl
theorem sub411 (p : Pattern) : d311 (change p 10000 none) = d311 p := by
  change (if p 49 then d310 (change p 10000 none) else d101 (change p 10000 none)) = d311 p
  rw [sub410, sub96]
  rfl
theorem sub412 (p : Pattern) : d312 (change p 10000 none) = d312 p := by
  change (if p 48 then d311 (change p 10000 none) else d169 (change p 10000 none)) = d312 p
  rw [sub411, sub168]
  rfl
theorem sub413 (p : Pattern) : d0 (change p 10000 (some 48)) = d0 p := by
  rfl
theorem sub414 (p : Pattern) : d12 (change p 10000 (some 48)) = d12 p := by
  rfl
theorem sub415 (p : Pattern) : d13 (change p 10000 (some 48)) = d13 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d0 (change p 10000 (some 48))) = d13 p
  rw [sub414, sub413]
  rfl
theorem sub416 (p : Pattern) : d14 (change p 10000 (some 48)) = d14 p := by
  change (if p 246 then d13 (change p 10000 (some 48)) else d0 (change p 10000 (some 48))) = d14 p
  rw [sub415, sub413]
  rfl
theorem sub417 (p : Pattern) : d15 (change p 10000 (some 48)) = d15 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d14 (change p 10000 (some 48))) = d15 p
  rw [sub414, sub416]
  rfl
theorem sub418 (p : Pattern) : d16 (change p 10000 (some 48)) = d16 p := by
  change (if p 182 then d15 (change p 10000 (some 48)) else d14 (change p 10000 (some 48))) = d16 p
  rw [sub417, sub416]
  rfl
theorem sub419 (p : Pattern) : d4 (change p 10000 (some 48)) = d4 p := by
  rfl
theorem sub420 (p : Pattern) : d17 (change p 10000 (some 48)) = d17 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d4 (change p 10000 (some 48))) = d17 p
  rw [sub414, sub419]
  rfl
theorem sub421 (p : Pattern) : d18 (change p 10000 (some 48)) = d18 p := by
  change (if p 246 then d17 (change p 10000 (some 48)) else d4 (change p 10000 (some 48))) = d18 p
  rw [sub420, sub419]
  rfl
theorem sub422 (p : Pattern) : d19 (change p 10000 (some 48)) = d19 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d18 (change p 10000 (some 48))) = d19 p
  rw [sub414, sub421]
  rfl
theorem sub423 (p : Pattern) : d20 (change p 10000 (some 48)) = d20 p := by
  change (if p 182 then d19 (change p 10000 (some 48)) else d18 (change p 10000 (some 48))) = d20 p
  rw [sub422, sub421]
  rfl
theorem sub424 (p : Pattern) : d21 (change p 10000 (some 48)) = d21 p := by
  change (if p 163 then d20 (change p 10000 (some 48)) else d16 (change p 10000 (some 48))) = d21 p
  rw [sub423, sub418]
  rfl
theorem sub425 (p : Pattern) : d22 (change p 10000 (some 48)) = d22 p := by
  change (if p 162 then d21 (change p 10000 (some 48)) else d16 (change p 10000 (some 48))) = d22 p
  rw [sub424, sub418]
  rfl
theorem sub426 (p : Pattern) : d9 (change p 10000 (some 48)) = d9 p := by
  rfl
theorem sub427 (p : Pattern) : d23 (change p 10000 (some 48)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d9 (change p 10000 (some 48))) = d23 p
  rw [sub414, sub426]
  rfl
theorem sub428 (p : Pattern) : d24 (change p 10000 (some 48)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 48)) else d9 (change p 10000 (some 48))) = d24 p
  rw [sub427, sub426]
  rfl
theorem sub429 (p : Pattern) : d25 (change p 10000 (some 48)) = d25 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d24 (change p 10000 (some 48))) = d25 p
  rw [sub414, sub428]
  rfl
theorem sub430 (p : Pattern) : d26 (change p 10000 (some 48)) = d26 p := by
  change (if p 182 then d25 (change p 10000 (some 48)) else d24 (change p 10000 (some 48))) = d26 p
  rw [sub429, sub428]
  rfl
theorem sub431 (p : Pattern) : d27 (change p 10000 (some 48)) = d27 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d26 (change p 10000 (some 48))) = d27 p
  rw [sub414, sub430]
  rfl
theorem sub432 (p : Pattern) : d28 (change p 10000 (some 48)) = d28 p := by
  change (if p 162 then d27 (change p 10000 (some 48)) else d21 (change p 10000 (some 48))) = d28 p
  rw [sub431, sub424]
  rfl
theorem sub433 (p : Pattern) : d29 (change p 10000 (some 48)) = d29 p := by
  change (if p 161 then d28 (change p 10000 (some 48)) else d22 (change p 10000 (some 48))) = d29 p
  rw [sub432, sub425]
  rfl
theorem sub434 (p : Pattern) : d2 (change p 10000 (some 48)) = d2 p := by
  rfl
theorem sub435 (p : Pattern) : d30 (change p 10000 (some 48)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d2 (change p 10000 (some 48))) = d30 p
  rw [sub414, sub434]
  rfl
theorem sub436 (p : Pattern) : d31 (change p 10000 (some 48)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 48)) else d2 (change p 10000 (some 48))) = d31 p
  rw [sub435, sub434]
  rfl
theorem sub437 (p : Pattern) : d32 (change p 10000 (some 48)) = d32 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d31 (change p 10000 (some 48))) = d32 p
  rw [sub414, sub436]
  rfl
theorem sub438 (p : Pattern) : d33 (change p 10000 (some 48)) = d33 p := by
  change (if p 182 then d32 (change p 10000 (some 48)) else d14 (change p 10000 (some 48))) = d33 p
  rw [sub437, sub416]
  rfl
theorem sub439 (p : Pattern) : d6 (change p 10000 (some 48)) = d6 p := by
  rfl
theorem sub440 (p : Pattern) : d34 (change p 10000 (some 48)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d6 (change p 10000 (some 48))) = d34 p
  rw [sub414, sub439]
  rfl
theorem sub441 (p : Pattern) : d35 (change p 10000 (some 48)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 48)) else d6 (change p 10000 (some 48))) = d35 p
  rw [sub440, sub439]
  rfl
theorem sub442 (p : Pattern) : d36 (change p 10000 (some 48)) = d36 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d35 (change p 10000 (some 48))) = d36 p
  rw [sub414, sub441]
  rfl
theorem sub443 (p : Pattern) : d37 (change p 10000 (some 48)) = d37 p := by
  change (if p 182 then d36 (change p 10000 (some 48)) else d14 (change p 10000 (some 48))) = d37 p
  rw [sub442, sub416]
  rfl
theorem sub444 (p : Pattern) : d38 (change p 10000 (some 48)) = d38 p := by
  change (if p 163 then d37 (change p 10000 (some 48)) else d33 (change p 10000 (some 48))) = d38 p
  rw [sub443, sub438]
  rfl
theorem sub445 (p : Pattern) : d11 (change p 10000 (some 48)) = d11 p := by
  rfl
theorem sub446 (p : Pattern) : d39 (change p 10000 (some 48)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d11 (change p 10000 (some 48))) = d39 p
  rw [sub414, sub445]
  rfl
theorem sub447 (p : Pattern) : d40 (change p 10000 (some 48)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 48)) else d11 (change p 10000 (some 48))) = d40 p
  rw [sub446, sub445]
  rfl
theorem sub448 (p : Pattern) : d41 (change p 10000 (some 48)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d40 (change p 10000 (some 48))) = d41 p
  rw [sub414, sub447]
  rfl
theorem sub449 (p : Pattern) : d42 (change p 10000 (some 48)) = d42 p := by
  change (if p 182 then d41 (change p 10000 (some 48)) else d14 (change p 10000 (some 48))) = d42 p
  rw [sub448, sub416]
  rfl
theorem sub450 (p : Pattern) : d43 (change p 10000 (some 48)) = d43 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d18 (change p 10000 (some 48))) = d43 p
  rw [sub414, sub421]
  rfl
theorem sub451 (p : Pattern) : d44 (change p 10000 (some 48)) = d44 p := by
  change (if p 163 then d43 (change p 10000 (some 48)) else d42 (change p 10000 (some 48))) = d44 p
  rw [sub450, sub449]
  rfl
theorem sub452 (p : Pattern) : d45 (change p 10000 (some 48)) = d45 p := by
  change (if p 162 then d44 (change p 10000 (some 48)) else d38 (change p 10000 (some 48))) = d45 p
  rw [sub451, sub444]
  rfl
theorem sub453 (p : Pattern) : d46 (change p 10000 (some 48)) = d46 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d14 (change p 10000 (some 48))) = d46 p
  rw [sub414, sub416]
  rfl
theorem sub454 (p : Pattern) : d47 (change p 10000 (some 48)) = d47 p := by
  change (if p 163 then d43 (change p 10000 (some 48)) else d46 (change p 10000 (some 48))) = d47 p
  rw [sub450, sub453]
  rfl
theorem sub455 (p : Pattern) : d48 (change p 10000 (some 48)) = d48 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d24 (change p 10000 (some 48))) = d48 p
  rw [sub414, sub428]
  rfl
theorem sub456 (p : Pattern) : d49 (change p 10000 (some 48)) = d49 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d48 (change p 10000 (some 48))) = d49 p
  rw [sub414, sub455]
  rfl
theorem sub457 (p : Pattern) : d50 (change p 10000 (some 48)) = d50 p := by
  change (if p 162 then d49 (change p 10000 (some 48)) else d47 (change p 10000 (some 48))) = d50 p
  rw [sub456, sub454]
  rfl
theorem sub458 (p : Pattern) : d51 (change p 10000 (some 48)) = d51 p := by
  change (if p 161 then d50 (change p 10000 (some 48)) else d45 (change p 10000 (some 48))) = d51 p
  rw [sub457, sub452]
  rfl
theorem sub459 (p : Pattern) : d52 (change p 10000 (some 48)) = d52 p := by
  change (if p 160 then d51 (change p 10000 (some 48)) else d29 (change p 10000 (some 48))) = d52 p
  rw [sub458, sub433]
  rfl
theorem sub460 (p : Pattern) : d53 (change p 10000 (some 48)) = d53 p := by
  change (if p 182 then d32 (change p 10000 (some 48)) else d31 (change p 10000 (some 48))) = d53 p
  rw [sub437, sub436]
  rfl
theorem sub461 (p : Pattern) : d54 (change p 10000 (some 48)) = d54 p := by
  change (if p 163 then d53 (change p 10000 (some 48)) else d16 (change p 10000 (some 48))) = d54 p
  rw [sub460, sub418]
  rfl
theorem sub462 (p : Pattern) : d55 (change p 10000 (some 48)) = d55 p := by
  change (if p 163 then d26 (change p 10000 (some 48)) else d20 (change p 10000 (some 48))) = d55 p
  rw [sub430, sub423]
  rfl
theorem sub463 (p : Pattern) : d56 (change p 10000 (some 48)) = d56 p := by
  change (if p 162 then d55 (change p 10000 (some 48)) else d54 (change p 10000 (some 48))) = d56 p
  rw [sub462, sub461]
  rfl
theorem sub464 (p : Pattern) : d10 (change p 10000 (some 48)) = d10 p := by
  rfl
theorem sub465 (p : Pattern) : d57 (change p 10000 (some 48)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d10 (change p 10000 (some 48))) = d57 p
  rw [sub414, sub464]
  rfl
theorem sub466 (p : Pattern) : d58 (change p 10000 (some 48)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 48)) else d10 (change p 10000 (some 48))) = d58 p
  rw [sub465, sub464]
  rfl
theorem sub467 (p : Pattern) : d59 (change p 10000 (some 48)) = d59 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d58 (change p 10000 (some 48))) = d59 p
  rw [sub414, sub466]
  rfl
theorem sub468 (p : Pattern) : d60 (change p 10000 (some 48)) = d60 p := by
  change (if p 182 then d59 (change p 10000 (some 48)) else d58 (change p 10000 (some 48))) = d60 p
  rw [sub467, sub466]
  rfl
theorem sub469 (p : Pattern) : d61 (change p 10000 (some 48)) = d61 p := by
  change (if p 163 then d60 (change p 10000 (some 48)) else d20 (change p 10000 (some 48))) = d61 p
  rw [sub468, sub423]
  rfl
theorem sub470 (p : Pattern) : d62 (change p 10000 (some 48)) = d62 p := by
  change (if p 182 then d41 (change p 10000 (some 48)) else d40 (change p 10000 (some 48))) = d62 p
  rw [sub448, sub447]
  rfl
theorem sub471 (p : Pattern) : d63 (change p 10000 (some 48)) = d63 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d62 (change p 10000 (some 48))) = d63 p
  rw [sub414, sub470]
  rfl
theorem sub472 (p : Pattern) : d64 (change p 10000 (some 48)) = d64 p := by
  change (if p 162 then d63 (change p 10000 (some 48)) else d61 (change p 10000 (some 48))) = d64 p
  rw [sub471, sub469]
  rfl
theorem sub473 (p : Pattern) : d65 (change p 10000 (some 48)) = d65 p := by
  change (if p 161 then d64 (change p 10000 (some 48)) else d56 (change p 10000 (some 48))) = d65 p
  rw [sub472, sub463]
  rfl
theorem sub474 (p : Pattern) : d66 (change p 10000 (some 48)) = d66 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d31 (change p 10000 (some 48))) = d66 p
  rw [sub414, sub436]
  rfl
theorem sub475 (p : Pattern) : d67 (change p 10000 (some 48)) = d67 p := by
  change (if p 163 then d66 (change p 10000 (some 48)) else d37 (change p 10000 (some 48))) = d67 p
  rw [sub474, sub443]
  rfl
theorem sub476 (p : Pattern) : d68 (change p 10000 (some 48)) = d68 p := by
  change (if p 163 then d48 (change p 10000 (some 48)) else d43 (change p 10000 (some 48))) = d68 p
  rw [sub455, sub450]
  rfl
theorem sub477 (p : Pattern) : d69 (change p 10000 (some 48)) = d69 p := by
  change (if p 162 then d68 (change p 10000 (some 48)) else d67 (change p 10000 (some 48))) = d69 p
  rw [sub476, sub475]
  rfl
theorem sub478 (p : Pattern) : d70 (change p 10000 (some 48)) = d70 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d58 (change p 10000 (some 48))) = d70 p
  rw [sub414, sub466]
  rfl
theorem sub479 (p : Pattern) : d71 (change p 10000 (some 48)) = d71 p := by
  change (if p 163 then d70 (change p 10000 (some 48)) else d43 (change p 10000 (some 48))) = d71 p
  rw [sub478, sub450]
  rfl
end NetHack.Sokoban22Refined85
