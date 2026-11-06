/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5320 (p : Pattern) (guard : d857 p = 1) : d407 p ≤ (2 : Int) + d195 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d407, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5316 p hg
    simpa only [d407, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d407, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5319 p hg
    simpa only [d407, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5321 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (2 : Int) + d196 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d408, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d408, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d408, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5320 p hg
    simpa only [d408, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5322 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (2 : Int) + d197 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5309 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5321 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5323 (p : Pattern) (guard : d858 p = 1) : d409 p ≤ (2 : Int) + d197 p := by
  cases selected : p 112 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5275 p hg
    simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5322 p hg
    simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5324 (p : Pattern) (guard : d0 p = 1) : d417 p ≤ (2 : Int) + d204 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5325 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (2 : Int) + d68 p := by
  omega
theorem compare5326 (p : Pattern) (guard : d857 p = 1) : d199 p ≤ (2 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5325 p hg
    simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5317 p hg
    simpa only [d857, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5327 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (2 : Int) + d70 p := by
  omega
theorem compare5328 (p : Pattern) (guard : d857 p = 1) : d200 p ≤ (2 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5327 p hg
    simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d857, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5329 (p : Pattern) (guard : d857 p = 1) : d201 p ≤ (2 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5326 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5328 p hg
    simpa only [d201, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5330 (p : Pattern) (guard : d857 p = 1) : d418 p ≤ (2 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d418, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5291 p hg
    simpa only [d418, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d418, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5329 p hg
    simpa only [d418, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5331 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (2 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d419, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5292 p hg
    simpa only [d419, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d419, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5330 p hg
    simpa only [d419, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5332 (p : Pattern) (guard : d857 p = 1) : d201 p ≤ (2 : Int) + d201 p := by
  omega
theorem compare5333 (p : Pattern) (guard : d857 p = 1) : d418 p ≤ (2 : Int) + d202 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d418, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d418, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d418, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5332 p hg
    simpa only [d418, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5334 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (2 : Int) + d203 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d419, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d419, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d419, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5333 p hg
    simpa only [d419, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5335 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (2 : Int) + d204 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5334 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5336 (p : Pattern) (guard : d858 p = 1) : d420 p ≤ (2 : Int) + d204 p := by
  cases selected : p 112 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d858, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5324 p hg
    simpa only [d858, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d858, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5335 p hg
    simpa only [d858, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5337 (p : Pattern) (guard : d858 p = 1) : d421 p ≤ (2 : Int) + d1386 p := by
  cases selected : p 106 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d421, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5323 p hg
    simpa only [d421, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d858 p = 1 := by simpa only [d421, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5336 p hg
    simpa only [d421, d1386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5338 (p : Pattern) (guard : d0 p = 1) : d437 p ≤ (2 : Int) + d1386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5339 (p : Pattern) (guard : d859 p = 1) : d438 p ≤ (2 : Int) + d1386 p := by
  cases selected : p 86 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d859, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5337 p hg
    simpa only [d859, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d859, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5338 p hg
    simpa only [d859, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5340 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (2 : Int) + d215 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5341 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5342 (p : Pattern) (guard : d857 p = 1) : d403 p ≤ (2 : Int) + d211 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d403, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5341 p hg
    simpa only [d857, d403, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d403, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d857, d403, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5343 (p : Pattern) (guard : d857 p = 1) : d404 p ≤ (2 : Int) + d212 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d404, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d404, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d404, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5342 p hg
    simpa only [d404, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5344 (p : Pattern) (guard : d857 p = 1) : d407 p ≤ (2 : Int) + d213 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d407, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5343 p hg
    simpa only [d407, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d407, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5319 p hg
    simpa only [d407, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5345 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (2 : Int) + d214 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d408, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d408, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d408, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5344 p hg
    simpa only [d408, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5346 (p : Pattern) (guard : d857 p = 1) : d408 p ≤ (2 : Int) + d215 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5309 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5345 p hg
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5347 (p : Pattern) (guard : d858 p = 1) : d409 p ≤ (2 : Int) + d215 p := by
  cases selected : p 112 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5340 p hg
    simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5346 p hg
    simpa only [d858, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5348 (p : Pattern) (guard : d0 p = 1) : d416 p ≤ (2 : Int) + d223 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5349 (p : Pattern) (guard : d857 p = 1) : d399 p ≤ (2 : Int) + d217 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3903 p hg
    simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3953 p hg
    simpa only [d857, d399, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5350 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (2 : Int) + d25 p := by
  omega
theorem compare5351 (p : Pattern) (guard : d857 p = 1) : d400 p ≤ (2 : Int) + d218 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5350 p hg
    simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d857, d400, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5352 (p : Pattern) (guard : d857 p = 1) : d401 p ≤ (2 : Int) + d219 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5349 p hg
    simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5351 p hg
    simpa only [d401, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5353 (p : Pattern) (guard : d857 p = 1) : d402 p ≤ (2 : Int) + d220 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5349 p hg
    simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5352 p hg
    simpa only [d402, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5354 (p : Pattern) (guard : d857 p = 1) : d418 p ≤ (2 : Int) + d221 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5352 p hg
    simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5332 p hg
    simpa only [d418, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5355 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (2 : Int) + d222 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5353 p hg
    simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5354 p hg
    simpa only [d419, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5356 (p : Pattern) (guard : d857 p = 1) : d419 p ≤ (2 : Int) + d223 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5355 p hg
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5357 (p : Pattern) (guard : d858 p = 1) : d439 p ≤ (2 : Int) + d223 p := by
  cases selected : p 112 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d858, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5348 p hg
    simpa only [d858, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d858, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5356 p hg
    simpa only [d858, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5358 (p : Pattern) (guard : d858 p = 1) : d440 p ≤ (2 : Int) + d1387 p := by
  cases selected : p 106 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d440, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5347 p hg
    simpa only [d440, d1387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d858 p = 1 := by simpa only [d440, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5357 p hg
    simpa only [d440, d1387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5359 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (2 : Int) + d1387 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5360 (p : Pattern) (guard : d859 p = 1) : d454 p ≤ (2 : Int) + d1387 p := by
  cases selected : p 86 with
  | false =>
    have hg : d858 p = 1 := by simpa only [d859, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5358 p hg
    simpa only [d859, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d859, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5359 p hg
    simpa only [d859, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5361 (p : Pattern) (guard : d859 p = 1) : d455 p ≤ (2 : Int) + d1388 p := by
  cases selected : p 80 with
  | false =>
    have hg : d859 p = 1 := by simpa only [d455, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5339 p hg
    simpa only [d455, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d859 p = 1 := by simpa only [d455, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5360 p hg
    simpa only [d455, d1388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5362 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d52 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5363 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d389, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d1092, d389, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d389, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d389, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5364 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5365 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d458 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5363 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5366 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d389, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d1092, d389, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d389, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d389, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5367 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5368 (p : Pattern) (guard : d1092 p = 1) : d390 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5369 (p : Pattern) (guard : d1092 p = 1) : d391 p ≤ (0 : Int) + d461 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d391, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5366 p hg
    simpa only [d391, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d391, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d391, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5370 (p : Pattern) (guard : d1092 p = 1) : d392 p ≤ (0 : Int) + d462 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d392, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5365 p hg
    simpa only [d392, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d392, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5369 p hg
    simpa only [d392, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5371 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5372 (p : Pattern) (guard : d1092 p = 1) : d393 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5373 (p : Pattern) (guard : d1092 p = 1) : d394 p ≤ (0 : Int) + d463 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d394, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5363 p hg
    simpa only [d394, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d394, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d394, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5374 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5375 (p : Pattern) (guard : d1092 p = 1) : d395 p ≤ (0 : Int) + d465 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d395, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1603 p hg
    simpa only [d1092, d395, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d395, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d1092, d395, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5376 (p : Pattern) (guard : d1092 p = 1) : d396 p ≤ (0 : Int) + d466 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d396, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d396, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d396, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d396, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5377 (p : Pattern) (guard : d1092 p = 1) : d397 p ≤ (0 : Int) + d467 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d397, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5373 p hg
    simpa only [d397, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d397, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5376 p hg
    simpa only [d397, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5378 (p : Pattern) (guard : d1092 p = 1) : d398 p ≤ (0 : Int) + d468 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d398, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5370 p hg
    simpa only [d398, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d398, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5377 p hg
    simpa only [d398, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5379 (p : Pattern) (guard : d1092 p = 1) : d399 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d399, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1794 p hg
    simpa only [d1092, d399, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d399, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d399, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5380 (p : Pattern) (guard : d1092 p = 1) : d399 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5381 (p : Pattern) (guard : d1092 p = 1) : d399 p ≤ (0 : Int) + d469 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5379 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5382 (p : Pattern) (guard : d1092 p = 1) : d400 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5383 (p : Pattern) (guard : d1092 p = 1) : d401 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d401, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d401, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d401, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5382 p hg
    simpa only [d401, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5384 (p : Pattern) (guard : d1092 p = 1) : d402 p ≤ (0 : Int) + d471 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d402, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5381 p hg
    simpa only [d402, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d402, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d402, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5385 (p : Pattern) (guard : d1092 p = 1) : d403 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1599 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5386 (p : Pattern) (guard : d1092 p = 1) : d404 p ≤ (0 : Int) + d472 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d404, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5379 p hg
    simpa only [d404, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d404, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5385 p hg
    simpa only [d404, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5387 (p : Pattern) (guard : d1092 p = 1) : d405 p ≤ (0 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5388 (p : Pattern) (guard : d1092 p = 1) : d406 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d406, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5387 p hg
    simpa only [d406, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d406, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5382 p hg
    simpa only [d406, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5389 (p : Pattern) (guard : d1092 p = 1) : d407 p ≤ (0 : Int) + d474 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d407, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5386 p hg
    simpa only [d407, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d407, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d407, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5390 (p : Pattern) (guard : d1092 p = 1) : d408 p ≤ (0 : Int) + d475 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d408, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d408, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d408, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5389 p hg
    simpa only [d408, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5391 (p : Pattern) (guard : d1092 p = 1) : d409 p ≤ (0 : Int) + d476 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d409, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5378 p hg
    simpa only [d409, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d409, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5390 p hg
    simpa only [d409, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5392 (p : Pattern) (guard : d1092 p = 1) : d391 p ≤ (0 : Int) + d477 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d391, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5363 p hg
    simpa only [d391, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d391, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d391, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5393 (p : Pattern) (guard : d1092 p = 1) : d410 p ≤ (0 : Int) + d479 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d410, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1632 p hg
    simpa only [d1092, d410, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d410, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1092, d410, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5394 (p : Pattern) (guard : d1092 p = 1) : d411 p ≤ (0 : Int) + d70 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1635 p hg
    simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1685 p hg
    simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5395 (p : Pattern) (guard : d1092 p = 1) : d412 p ≤ (0 : Int) + d480 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d412, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5393 p hg
    simpa only [d412, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d412, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5394 p hg
    simpa only [d412, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5396 (p : Pattern) (guard : d1092 p = 1) : d413 p ≤ (0 : Int) + d481 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d413, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5392 p hg
    simpa only [d413, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d413, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5395 p hg
    simpa only [d413, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5397 (p : Pattern) (guard : d1092 p = 1) : d414 p ≤ (0 : Int) + d482 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d414, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5370 p hg
    simpa only [d414, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d414, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5396 p hg
    simpa only [d414, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5398 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d484 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d389, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d1092, d389, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d389, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d389, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5399 (p : Pattern) (guard : d1092 p = 1) : d391 p ≤ (0 : Int) + d485 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d391, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d391, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d391, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d391, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5400 (p : Pattern) (guard : d1092 p = 1) : d415 p ≤ (0 : Int) + d486 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d415, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5399 p hg
    simpa only [d415, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d415, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d415, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5401 (p : Pattern) (guard : d1092 p = 1) : d416 p ≤ (0 : Int) + d487 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d416, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5370 p hg
    simpa only [d416, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d416, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d416, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5402 (p : Pattern) (guard : d1092 p = 1) : d417 p ≤ (0 : Int) + d488 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d417, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5397 p hg
    simpa only [d417, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d417, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5401 p hg
    simpa only [d417, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5403 (p : Pattern) (guard : d1092 p = 1) : d401 p ≤ (0 : Int) + d461 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d401, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5379 p hg
    simpa only [d401, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d401, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5382 p hg
    simpa only [d401, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5404 (p : Pattern) (guard : d1092 p = 1) : d418 p ≤ (0 : Int) + d489 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d418, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5403 p hg
    simpa only [d418, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d418, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d418, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5405 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d490 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d419, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d419, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d419, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5404 p hg
    simpa only [d419, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5406 (p : Pattern) (guard : d1092 p = 1) : d418 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d418, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d418, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d418, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d418, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5407 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d492 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d419, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d419, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d419, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5406 p hg
    simpa only [d419, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5408 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d493 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5405 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5407 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5409 (p : Pattern) (guard : d1092 p = 1) : d420 p ≤ (0 : Int) + d494 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d420, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5402 p hg
    simpa only [d420, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d420, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5408 p hg
    simpa only [d420, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5410 (p : Pattern) (guard : d1092 p = 1) : d421 p ≤ (0 : Int) + d495 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d421, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5391 p hg
    simpa only [d421, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d421, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5409 p hg
    simpa only [d421, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5411 (p : Pattern) (guard : d1092 p = 1) : d394 p ≤ (0 : Int) + d496 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d394, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d394, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d394, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d394, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5412 (p : Pattern) (guard : d1092 p = 1) : d395 p ≤ (0 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5413 (p : Pattern) (guard : d1092 p = 1) : d396 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d396, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5412 p hg
    simpa only [d396, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d396, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d396, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5414 (p : Pattern) (guard : d1092 p = 1) : d397 p ≤ (0 : Int) + d497 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d397, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5411 p hg
    simpa only [d397, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d397, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5413 p hg
    simpa only [d397, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5415 (p : Pattern) (guard : d1092 p = 1) : d398 p ≤ (0 : Int) + d498 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d398, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5370 p hg
    simpa only [d398, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d398, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5414 p hg
    simpa only [d398, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5416 (p : Pattern) (guard : d1092 p = 1) : d398 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5378 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5415 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5417 (p : Pattern) (guard : d1092 p = 1) : d422 p ≤ (0 : Int) + d501 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d422, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1817 p hg
    simpa only [d1092, d422, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d422, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d1092, d422, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5418 (p : Pattern) (guard : d1092 p = 1) : d422 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1820 p hg
    simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5419 (p : Pattern) (guard : d1092 p = 1) : d422 p ≤ (0 : Int) + d502 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5417 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5418 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5420 (p : Pattern) (guard : d1092 p = 1) : d423 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d423, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5418 p hg
    simpa only [d423, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d423, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5394 p hg
    simpa only [d423, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5421 (p : Pattern) (guard : d1092 p = 1) : d424 p ≤ (0 : Int) + d503 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d424, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5419 p hg
    simpa only [d424, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d424, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5420 p hg
    simpa only [d424, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5422 (p : Pattern) (guard : d1092 p = 1) : d423 p ≤ (0 : Int) + d504 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d423, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5417 p hg
    simpa only [d423, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d423, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5394 p hg
    simpa only [d423, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5423 (p : Pattern) (guard : d1092 p = 1) : d410 p ≤ (0 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5424 (p : Pattern) (guard : d1092 p = 1) : d412 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d412, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5423 p hg
    simpa only [d412, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d412, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5394 p hg
    simpa only [d412, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5425 (p : Pattern) (guard : d1092 p = 1) : d425 p ≤ (0 : Int) + d505 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d425, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5422 p hg
    simpa only [d425, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d425, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5424 p hg
    simpa only [d425, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5426 (p : Pattern) (guard : d1092 p = 1) : d426 p ≤ (0 : Int) + d506 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d426, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5421 p hg
    simpa only [d426, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d426, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5425 p hg
    simpa only [d426, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5427 (p : Pattern) (guard : d1092 p = 1) : d425 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d425, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5420 p hg
    simpa only [d425, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d425, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5424 p hg
    simpa only [d425, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5428 (p : Pattern) (guard : d1092 p = 1) : d426 p ≤ (0 : Int) + d507 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d426, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5421 p hg
    simpa only [d426, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d426, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5427 p hg
    simpa only [d426, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5429 (p : Pattern) (guard : d1092 p = 1) : d426 p ≤ (0 : Int) + d508 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5426 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5428 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5430 (p : Pattern) (guard : d1092 p = 1) : d427 p ≤ (0 : Int) + d509 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d427, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5416 p hg
    simpa only [d427, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d427, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5429 p hg
    simpa only [d427, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5431 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d510 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5432 (p : Pattern) (guard : d1092 p = 1) : d391 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d391, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d391, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d391, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d391, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5433 (p : Pattern) (guard : d1092 p = 1) : d392 p ≤ (0 : Int) + d511 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d392, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5431 p hg
    simpa only [d392, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d392, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5432 p hg
    simpa only [d392, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5434 (p : Pattern) (guard : d1092 p = 1) : d415 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d415, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5432 p hg
    simpa only [d415, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d415, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d415, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5435 (p : Pattern) (guard : d1092 p = 1) : d416 p ≤ (0 : Int) + d512 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d416, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d416, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d416, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5434 p hg
    simpa only [d416, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5436 (p : Pattern) (guard : d1092 p = 1) : d416 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5401 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5437 (p : Pattern) (guard : d1092 p = 1) : d428 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d428, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5420 p hg
    simpa only [d428, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d428, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d428, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5438 (p : Pattern) (guard : d1092 p = 1) : d429 p ≤ (0 : Int) + d514 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d429, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5421 p hg
    simpa only [d429, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d429, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d429, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5439 (p : Pattern) (guard : d1092 p = 1) : d430 p ≤ (0 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d1092, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5440 (p : Pattern) (guard : d1092 p = 1) : d431 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5439 p hg
    simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1686 p hg
    simpa only [d431, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5441 (p : Pattern) (guard : d1092 p = 1) : d432 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5439 p hg
    simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d432, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5442 (p : Pattern) (guard : d1092 p = 1) : d433 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d433, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5443 (p : Pattern) (guard : d1092 p = 1) : d434 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5441 p hg
    simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5442 p hg
    simpa only [d434, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5444 (p : Pattern) (guard : d1092 p = 1) : d435 p ≤ (0 : Int) + d515 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d435, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5438 p hg
    simpa only [d435, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d435, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5443 p hg
    simpa only [d435, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5445 (p : Pattern) (guard : d1092 p = 1) : d436 p ≤ (0 : Int) + d516 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d436, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5436 p hg
    simpa only [d436, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d436, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5444 p hg
    simpa only [d436, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5446 (p : Pattern) (guard : d1092 p = 1) : d437 p ≤ (0 : Int) + d517 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d437, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5430 p hg
    simpa only [d437, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d437, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5445 p hg
    simpa only [d437, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5447 (p : Pattern) (guard : d1092 p = 1) : d438 p ≤ (0 : Int) + d518 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d438, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5410 p hg
    simpa only [d438, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d438, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5446 p hg
    simpa only [d438, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5448 (p : Pattern) (guard : d1092 p = 1) : d404 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d404, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d404, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d404, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5385 p hg
    simpa only [d404, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5449 (p : Pattern) (guard : d1092 p = 1) : d407 p ≤ (0 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d407, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5448 p hg
    simpa only [d407, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d407, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d407, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5450 (p : Pattern) (guard : d1092 p = 1) : d408 p ≤ (0 : Int) + d521 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d408, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d408, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d408, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d408, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5451 (p : Pattern) (guard : d1092 p = 1) : d408 p ≤ (0 : Int) + d522 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5390 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5450 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5452 (p : Pattern) (guard : d1092 p = 1) : d409 p ≤ (0 : Int) + d523 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d409, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5416 p hg
    simpa only [d409, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d409, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5451 p hg
    simpa only [d409, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5453 (p : Pattern) (guard : d1092 p = 1) : d402 p ≤ (0 : Int) + d524 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d402, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d402, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d402, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d402, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5454 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d525 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d419, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5453 p hg
    simpa only [d419, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d419, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5406 p hg
    simpa only [d419, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5455 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d526 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5407 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5456 (p : Pattern) (guard : d1092 p = 1) : d439 p ≤ (0 : Int) + d527 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d439, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5436 p hg
    simpa only [d439, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d439, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d439, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5457 (p : Pattern) (guard : d1092 p = 1) : d440 p ≤ (0 : Int) + d528 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d440, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d440, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d440, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5456 p hg
    simpa only [d440, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5458 (p : Pattern) (guard : d1092 p = 1) : d441 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1717 p hg
    simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5459 (p : Pattern) (guard : d1092 p = 1) : d442 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d442, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d442, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d442, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5458 p hg
    simpa only [d442, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
