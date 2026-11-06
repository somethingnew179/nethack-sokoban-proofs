/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons208
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29260 (p : Pattern) (guard : d0 p = 1) : d3569 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29261 (p : Pattern) (guard : d5850 p = 1) : d3570 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3570, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d5850, d3570, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3570, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29260 p hg
    simpa only [d5850, d3570, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29262 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (0 : Int) + d1701 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5843, d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d5843, d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29263 (p : Pattern) (guard : d5843 p = 1) : d3569 p ≤ (0 : Int) + d1702 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3569, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29262 p hg
    simpa only [d3569, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3569, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d3569, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29264 (p : Pattern) (guard : d5850 p = 1) : d3569 p ≤ (0 : Int) + d2533 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29263 p hg
    simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29260 p hg
    simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29265 (p : Pattern) (guard : d5850 p = 1) : d3571 p ≤ (0 : Int) + d2534 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3571, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29261 p hg
    simpa only [d3571, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3571, d2534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29264 p hg
    simpa only [d3571, d2534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29266 (p : Pattern) (guard : d5850 p = 1) : d3572 p ≤ (0 : Int) + d2535 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3572, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29265 p hg
    simpa only [d3572, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3572, d2535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3572, d2535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29267 (p : Pattern) (guard : d5850 p = 1) : d3573 p ≤ (0 : Int) + d2536 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3573, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29259 p hg
    simpa only [d3573, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3573, d2536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29266 p hg
    simpa only [d3573, d2536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29268 (p : Pattern) (guard : d5850 p = 1) : d3574 p ≤ (0 : Int) + d2537 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3574, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29267 p hg
    simpa only [d3574, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3574, d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3574, d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29269 (p : Pattern) (guard : d5850 p = 1) : d3575 p ≤ (0 : Int) + d2538 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3575, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29252 p hg
    simpa only [d3575, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3575, d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29268 p hg
    simpa only [d3575, d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29270 (p : Pattern) (guard : d5850 p = 1) : d3576 p ≤ (0 : Int) + d2539 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3576, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29253 p hg
    simpa only [d3576, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3576, d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29269 p hg
    simpa only [d3576, d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29271 (p : Pattern) (guard : d0 p = 1) : d3577 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29272 (p : Pattern) (guard : d5850 p = 1) : d3578 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3578, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5850, d3578, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3578, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29271 p hg
    simpa only [d5850, d3578, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29273 (p : Pattern) (guard : d0 p = 1) : d3579 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29274 (p : Pattern) (guard : d5850 p = 1) : d3580 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3580, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d5850, d3580, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3580, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29273 p hg
    simpa only [d5850, d3580, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29275 (p : Pattern) (guard : d5850 p = 1) : d3581 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3581, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29272 p hg
    simpa only [d3581, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3581, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29274 p hg
    simpa only [d3581, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29276 (p : Pattern) (guard : d5850 p = 1) : d3582 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3582, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d3582, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3582, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29275 p hg
    simpa only [d3582, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29277 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19917 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29278 (p : Pattern) (guard : d0 p = 1) : d3583 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29279 (p : Pattern) (guard : d5850 p = 1) : d3584 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3584, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5850, d3584, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3584, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29278 p hg
    simpa only [d5850, d3584, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29280 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d1713 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d30, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d5843, d30, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29281 (p : Pattern) (guard : d5843 p = 1) : d3585 p ≤ (0 : Int) + d1714 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3585, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29280 p hg
    simpa only [d3585, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3585, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d3585, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29282 (p : Pattern) (guard : d5850 p = 1) : d3586 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3586, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d5850, d3586, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3586, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17126 p hg
    simpa only [d5850, d3586, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29283 (p : Pattern) (guard : d5850 p = 1) : d3587 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3587, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29279 p hg
    simpa only [d3587, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3587, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29282 p hg
    simpa only [d3587, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29284 (p : Pattern) (guard : d5850 p = 1) : d3588 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3588, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29283 p hg
    simpa only [d3588, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3588, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3588, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29285 (p : Pattern) (guard : d5850 p = 1) : d3589 p ≤ (0 : Int) + d2544 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3589, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29276 p hg
    simpa only [d3589, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3589, d2544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29284 p hg
    simpa only [d3589, d2544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29286 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29287 (p : Pattern) (guard : d5850 p = 1) : d3590 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3590, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29286 p hg
    simpa only [d5850, d3590, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3590, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5850, d3590, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29288 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (0 : Int) + d1721 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5843, d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d5843, d34, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29289 (p : Pattern) (guard : d5843 p = 1) : d3591 p ≤ (0 : Int) + d1722 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3591, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29288 p hg
    simpa only [d3591, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3591, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d3591, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29290 (p : Pattern) (guard : d5850 p = 1) : d3592 p ≤ (0 : Int) + d2546 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3592, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29289 p hg
    simpa only [d5850, d3592, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3592, d2546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17131 p hg
    simpa only [d5850, d3592, d2546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29291 (p : Pattern) (guard : d5850 p = 1) : d3593 p ≤ (0 : Int) + d2547 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3593, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29287 p hg
    simpa only [d3593, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3593, d2547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29290 p hg
    simpa only [d3593, d2547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29292 (p : Pattern) (guard : d5850 p = 1) : d3594 p ≤ (0 : Int) + d2548 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3594, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29291 p hg
    simpa only [d3594, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3594, d2548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3594, d2548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29293 (p : Pattern) (guard : d5850 p = 1) : d3595 p ≤ (0 : Int) + d2549 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3595, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29276 p hg
    simpa only [d3595, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3595, d2549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29292 p hg
    simpa only [d3595, d2549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29294 (p : Pattern) (guard : d5850 p = 1) : d3596 p ≤ (0 : Int) + d2550 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3596, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29285 p hg
    simpa only [d3596, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3596, d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29293 p hg
    simpa only [d3596, d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29295 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23452 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29296 (p : Pattern) (guard : d5850 p = 1) : d3597 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3597, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29295 p hg
    simpa only [d5850, d3597, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3597, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5850, d3597, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29297 (p : Pattern) (guard : d5850 p = 1) : d327 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20591 p hg
    simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29298 (p : Pattern) (guard : d5850 p = 1) : d3598 p ≤ (0 : Int) + d2552 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3598, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29296 p hg
    simpa only [d3598, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3598, d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29297 p hg
    simpa only [d3598, d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29299 (p : Pattern) (guard : d5850 p = 1) : d3599 p ≤ (0 : Int) + d2553 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3599, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29298 p hg
    simpa only [d3599, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3599, d2553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3599, d2553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29300 (p : Pattern) (guard : d5850 p = 1) : d3600 p ≤ (0 : Int) + d2554 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3600, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29276 p hg
    simpa only [d3600, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3600, d2554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29299 p hg
    simpa only [d3600, d2554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29301 (p : Pattern) (guard : d0 p = 1) : d3601 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29302 (p : Pattern) (guard : d5850 p = 1) : d3602 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3602, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5850, d3602, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3602, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29301 p hg
    simpa only [d5850, d3602, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29303 (p : Pattern) (guard : d5850 p = 1) : d3603 p ≤ (0 : Int) + d2521 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3603, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d5850, d3603, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3603, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17223 p hg
    simpa only [d5850, d3603, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29304 (p : Pattern) (guard : d5850 p = 1) : d3604 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3604, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29302 p hg
    simpa only [d3604, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3604, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29303 p hg
    simpa only [d3604, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29305 (p : Pattern) (guard : d5850 p = 1) : d3605 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3605, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29236 p hg
    simpa only [d3605, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3605, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29304 p hg
    simpa only [d3605, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29306 (p : Pattern) (guard : d5850 p = 1) : d3606 p ≤ (0 : Int) + d2555 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3606, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29305 p hg
    simpa only [d3606, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3606, d2555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3606, d2555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29307 (p : Pattern) (guard : d5850 p = 1) : d3607 p ≤ (0 : Int) + d2556 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3607, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29300 p hg
    simpa only [d3607, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3607, d2556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29306 p hg
    simpa only [d3607, d2556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29308 (p : Pattern) (guard : d5850 p = 1) : d3608 p ≤ (0 : Int) + d2557 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3608, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29294 p hg
    simpa only [d3608, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3608, d2557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29307 p hg
    simpa only [d3608, d2557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29309 (p : Pattern) (guard : d5850 p = 1) : d3609 p ≤ (0 : Int) + d2558 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3609, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29276 p hg
    simpa only [d3609, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3609, d2558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3609, d2558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29310 (p : Pattern) (guard : d5850 p = 1) : d3610 p ≤ (0 : Int) + d2559 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3610, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29309 p hg
    simpa only [d3610, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3610, d2559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29306 p hg
    simpa only [d3610, d2559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29311 (p : Pattern) (guard : d5850 p = 1) : d3611 p ≤ (0 : Int) + d2560 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3611, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29259 p hg
    simpa only [d3611, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3611, d2560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3611, d2560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29312 (p : Pattern) (guard : d5850 p = 1) : d3612 p ≤ (0 : Int) + d2561 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3612, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29311 p hg
    simpa only [d3612, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3612, d2561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3612, d2561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29313 (p : Pattern) (guard : d5850 p = 1) : d3613 p ≤ (0 : Int) + d2562 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3613, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29310 p hg
    simpa only [d3613, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3613, d2562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29312 p hg
    simpa only [d3613, d2562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29314 (p : Pattern) (guard : d5850 p = 1) : d3614 p ≤ (0 : Int) + d2563 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3614, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29308 p hg
    simpa only [d3614, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3614, d2563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29313 p hg
    simpa only [d3614, d2563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29315 (p : Pattern) (guard : d5850 p = 1) : d3615 p ≤ (0 : Int) + d2564 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3615, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29270 p hg
    simpa only [d3615, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3615, d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29314 p hg
    simpa only [d3615, d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29316 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29317 (p : Pattern) (guard : d5843 p = 1) : d1785 p ≤ (0 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29316 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29318 (p : Pattern) (guard : d5843 p = 1) : d3616 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3616, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29317 p hg
    simpa only [d3616, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3616, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d3616, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29319 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29320 (p : Pattern) (guard : d5850 p = 1) : d3617 p ≤ (0 : Int) + d2565 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3617, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29318 p hg
    simpa only [d5850, d3617, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3617, d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29319 p hg
    simpa only [d5850, d3617, d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29321 (p : Pattern) (guard : d5850 p = 1) : d3618 p ≤ (0 : Int) + d2566 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3618, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29320 p hg
    simpa only [d3618, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3618, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d3618, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29322 (p : Pattern) (guard : d5850 p = 1) : d3619 p ≤ (0 : Int) + d2567 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3619, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29321 p hg
    simpa only [d3619, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3619, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d3619, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29323 (p : Pattern) (guard : d5850 p = 1) : d3620 p ≤ (0 : Int) + d2568 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3620, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29322 p hg
    simpa only [d3620, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3620, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29225 p hg
    simpa only [d3620, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29324 (p : Pattern) (guard : d5850 p = 1) : d30 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29325 (p : Pattern) (guard : d0 p = 1) : d3585 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29326 (p : Pattern) (guard : d5850 p = 1) : d3621 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3621, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5850, d3621, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3621, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d5850, d3621, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29327 (p : Pattern) (guard : d5850 p = 1) : d3585 p ≤ (0 : Int) + d2541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29328 (p : Pattern) (guard : d5850 p = 1) : d3622 p ≤ (0 : Int) + d2542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3622, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29326 p hg
    simpa only [d3622, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3622, d2542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29327 p hg
    simpa only [d3622, d2542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29329 (p : Pattern) (guard : d5850 p = 1) : d3623 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3623, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29324 p hg
    simpa only [d3623, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3623, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29328 p hg
    simpa only [d3623, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29330 (p : Pattern) (guard : d0 p = 1) : d3624 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29331 (p : Pattern) (guard : d5850 p = 1) : d3625 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3625, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5850, d3625, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3625, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29330 p hg
    simpa only [d5850, d3625, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29332 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d1742 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d30, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26339 p hg
    simpa only [d5843, d30, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29333 (p : Pattern) (guard : d5843 p = 1) : d3624 p ≤ (0 : Int) + d1743 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3624, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29332 p hg
    simpa only [d3624, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3624, d1743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19861 p hg
    simpa only [d3624, d1743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29334 (p : Pattern) (guard : d5850 p = 1) : d3624 p ≤ (0 : Int) + d2570 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29333 p hg
    simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29330 p hg
    simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29335 (p : Pattern) (guard : d5850 p = 1) : d3626 p ≤ (0 : Int) + d2571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3626, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29331 p hg
    simpa only [d3626, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3626, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29334 p hg
    simpa only [d3626, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29336 (p : Pattern) (guard : d5850 p = 1) : d3627 p ≤ (0 : Int) + d2572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3627, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29335 p hg
    simpa only [d3627, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3627, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3627, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29337 (p : Pattern) (guard : d5850 p = 1) : d3628 p ≤ (0 : Int) + d2573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3628, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29329 p hg
    simpa only [d3628, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3628, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29336 p hg
    simpa only [d3628, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29338 (p : Pattern) (guard : d5850 p = 1) : d3629 p ≤ (0 : Int) + d2574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3629, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29323 p hg
    simpa only [d3629, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3629, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29337 p hg
    simpa only [d3629, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29339 (p : Pattern) (guard : d5850 p = 1) : d3630 p ≤ (0 : Int) + d2575 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3630, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29251 p hg
    simpa only [d3630, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3630, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29267 p hg
    simpa only [d3630, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29340 (p : Pattern) (guard : d5850 p = 1) : d3631 p ≤ (0 : Int) + d2576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3631, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29338 p hg
    simpa only [d3631, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3631, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29339 p hg
    simpa only [d3631, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29341 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23494 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29342 (p : Pattern) (guard : d5850 p = 1) : d57 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29341 p hg
    simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29343 (p : Pattern) (guard : d5850 p = 1) : d3632 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3632, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29341 p hg
    simpa only [d5850, d3632, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3632, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5850, d3632, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29344 (p : Pattern) (guard : d5850 p = 1) : d329 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20634 p hg
    simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29345 (p : Pattern) (guard : d5850 p = 1) : d3633 p ≤ (0 : Int) + d2578 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3633, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29343 p hg
    simpa only [d3633, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3633, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29344 p hg
    simpa only [d3633, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29346 (p : Pattern) (guard : d5850 p = 1) : d3634 p ≤ (0 : Int) + d2579 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3634, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29342 p hg
    simpa only [d3634, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3634, d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29345 p hg
    simpa only [d3634, d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29347 (p : Pattern) (guard : d5850 p = 1) : d3635 p ≤ (0 : Int) + d2580 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3635, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29345 p hg
    simpa only [d3635, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3635, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3635, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29348 (p : Pattern) (guard : d5850 p = 1) : d3636 p ≤ (0 : Int) + d2581 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3636, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29346 p hg
    simpa only [d3636, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3636, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29347 p hg
    simpa only [d3636, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29349 (p : Pattern) (guard : d5850 p = 1) : d3637 p ≤ (0 : Int) + d2582 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3637, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29251 p hg
    simpa only [d3637, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3637, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29348 p hg
    simpa only [d3637, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29350 (p : Pattern) (guard : d5850 p = 1) : d39 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29295 p hg
    simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29351 (p : Pattern) (guard : d5850 p = 1) : d3638 p ≤ (0 : Int) + d2583 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3638, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29350 p hg
    simpa only [d3638, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3638, d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29298 p hg
    simpa only [d3638, d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29352 (p : Pattern) (guard : d5850 p = 1) : d3639 p ≤ (0 : Int) + d2584 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3639, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29351 p hg
    simpa only [d3639, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3639, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29299 p hg
    simpa only [d3639, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29353 (p : Pattern) (guard : d5850 p = 1) : d3640 p ≤ (0 : Int) + d2585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3640, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d3640, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3640, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3640, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29354 (p : Pattern) (guard : d5850 p = 1) : d3641 p ≤ (0 : Int) + d2586 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3641, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29349 p hg
    simpa only [d3641, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3641, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29353 p hg
    simpa only [d3641, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29355 (p : Pattern) (guard : d5850 p = 1) : d3642 p ≤ (0 : Int) + d2587 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3642, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29340 p hg
    simpa only [d3642, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3642, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29354 p hg
    simpa only [d3642, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29356 (p : Pattern) (guard : d5850 p = 1) : d3643 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3643, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29324 p hg
    simpa only [d3643, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3643, d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29283 p hg
    simpa only [d3643, d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29357 (p : Pattern) (guard : d5850 p = 1) : d3644 p ≤ (0 : Int) + d2588 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3644, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29356 p hg
    simpa only [d3644, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3644, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3644, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29358 (p : Pattern) (guard : d5850 p = 1) : d3645 p ≤ (0 : Int) + d2589 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3645, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29293 p hg
    simpa only [d3645, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3645, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29357 p hg
    simpa only [d3645, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29359 (p : Pattern) (guard : d5850 p = 1) : d3646 p ≤ (0 : Int) + d2590 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3646, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29306 p hg
    simpa only [d3646, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3646, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29311 p hg
    simpa only [d3646, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29360 (p : Pattern) (guard : d5850 p = 1) : d3647 p ≤ (0 : Int) + d2591 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3647, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29358 p hg
    simpa only [d3647, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3647, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29359 p hg
    simpa only [d3647, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29361 (p : Pattern) (guard : d5850 p = 1) : d3648 p ≤ (0 : Int) + d2592 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3648, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29346 p hg
    simpa only [d3648, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3648, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3648, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29362 (p : Pattern) (guard : d5850 p = 1) : d3649 p ≤ (0 : Int) + d2593 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3649, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29306 p hg
    simpa only [d3649, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3649, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29361 p hg
    simpa only [d3649, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29363 (p : Pattern) (guard : d5850 p = 1) : d3650 p ≤ (0 : Int) + d2594 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3650, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29351 p hg
    simpa only [d3650, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3650, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3650, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29364 (p : Pattern) (guard : d5850 p = 1) : d3651 p ≤ (0 : Int) + d2595 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3651, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29363 p hg
    simpa only [d3651, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3651, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3651, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29365 (p : Pattern) (guard : d5850 p = 1) : d3652 p ≤ (0 : Int) + d2596 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3652, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29362 p hg
    simpa only [d3652, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3652, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29364 p hg
    simpa only [d3652, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29366 (p : Pattern) (guard : d5850 p = 1) : d3653 p ≤ (0 : Int) + d2597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3653, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29360 p hg
    simpa only [d3653, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3653, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29365 p hg
    simpa only [d3653, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29367 (p : Pattern) (guard : d5850 p = 1) : d3654 p ≤ (0 : Int) + d2598 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3654, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29355 p hg
    simpa only [d3654, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3654, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29366 p hg
    simpa only [d3654, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29368 (p : Pattern) (guard : d5850 p = 1) : d3655 p ≤ (0 : Int) + d2599 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3655, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29315 p hg
    simpa only [d3655, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3655, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29367 p hg
    simpa only [d3655, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29369 (p : Pattern) (guard : d5850 p = 1) : d3656 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3656, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d5850, d3656, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3656, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29271 p hg
    simpa only [d5850, d3656, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29370 (p : Pattern) (guard : d5850 p = 1) : d3657 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3657, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29272 p hg
    simpa only [d3657, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3657, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29369 p hg
    simpa only [d3657, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29371 (p : Pattern) (guard : d5850 p = 1) : d3658 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3658, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d3658, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3658, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29370 p hg
    simpa only [d3658, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29372 (p : Pattern) (guard : d5850 p = 1) : d3659 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3659, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d3659, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3659, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3659, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29373 (p : Pattern) (guard : d5850 p = 1) : d3660 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3660, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29371 p hg
    simpa only [d3660, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3660, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29372 p hg
    simpa only [d3660, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29374 (p : Pattern) (guard : d0 p = 1) : d3661 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29375 (p : Pattern) (guard : d5850 p = 1) : d3662 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3662, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d5850, d3662, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3662, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29374 p hg
    simpa only [d5850, d3662, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29376 (p : Pattern) (guard : d5850 p = 1) : d3663 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3663, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29272 p hg
    simpa only [d3663, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3663, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29375 p hg
    simpa only [d3663, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29377 (p : Pattern) (guard : d5850 p = 1) : d3664 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3664, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29376 p hg
    simpa only [d3664, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3664, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3664, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29378 (p : Pattern) (guard : d5850 p = 1) : d3665 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3665, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29276 p hg
    simpa only [d3665, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3665, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29377 p hg
    simpa only [d3665, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29379 (p : Pattern) (guard : d5850 p = 1) : d3666 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29373 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29378 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29380 (p : Pattern) (guard : d5850 p = 1) : d3667 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3667, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29275 p hg
    simpa only [d3667, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3667, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3667, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29381 (p : Pattern) (guard : d5850 p = 1) : d3668 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3668, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29276 p hg
    simpa only [d3668, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3668, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29380 p hg
    simpa only [d3668, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29382 (p : Pattern) (guard : d5850 p = 1) : d3669 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3669, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29304 p hg
    simpa only [d3669, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3669, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3669, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29383 (p : Pattern) (guard : d5850 p = 1) : d3670 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3670, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29305 p hg
    simpa only [d3670, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3670, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29382 p hg
    simpa only [d3670, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29384 (p : Pattern) (guard : d5850 p = 1) : d3671 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3671, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29381 p hg
    simpa only [d3671, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3671, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29383 p hg
    simpa only [d3671, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29385 (p : Pattern) (guard : d5850 p = 1) : d3672 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3672, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29379 p hg
    simpa only [d3672, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3672, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29384 p hg
    simpa only [d3672, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29386 (p : Pattern) (guard : d5850 p = 1) : d3673 p ≤ (0 : Int) + d2606 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3673, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29258 p hg
    simpa only [d3673, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3673, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3673, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29387 (p : Pattern) (guard : d5850 p = 1) : d3674 p ≤ (0 : Int) + d2607 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3674, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29259 p hg
    simpa only [d3674, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3674, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29386 p hg
    simpa only [d3674, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29388 (p : Pattern) (guard : d5850 p = 1) : d3675 p ≤ (0 : Int) + d2608 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3675, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29387 p hg
    simpa only [d3675, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3675, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3675, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29389 (p : Pattern) (guard : d5850 p = 1) : d3676 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3676, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29384 p hg
    simpa only [d3676, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3676, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29388 p hg
    simpa only [d3676, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29390 (p : Pattern) (guard : d5850 p = 1) : d3677 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3677, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29385 p hg
    simpa only [d3677, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3677, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29389 p hg
    simpa only [d3677, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29391 (p : Pattern) (guard : d5850 p = 1) : d3678 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3678, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29356 p hg
    simpa only [d3678, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3678, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29284 p hg
    simpa only [d3678, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29392 (p : Pattern) (guard : d5850 p = 1) : d34 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29286 p hg
    simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29393 (p : Pattern) (guard : d5850 p = 1) : d3679 p ≤ (0 : Int) + d2612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3679, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29392 p hg
    simpa only [d3679, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3679, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29291 p hg
    simpa only [d3679, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29394 (p : Pattern) (guard : d5850 p = 1) : d3680 p ≤ (0 : Int) + d2613 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3680, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29393 p hg
    simpa only [d3680, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3680, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29292 p hg
    simpa only [d3680, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29395 (p : Pattern) (guard : d5850 p = 1) : d3681 p ≤ (0 : Int) + d2614 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3681, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29391 p hg
    simpa only [d3681, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3681, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29394 p hg
    simpa only [d3681, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29396 (p : Pattern) (guard : d5850 p = 1) : d3682 p ≤ (0 : Int) + d2615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3682, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29395 p hg
    simpa only [d3682, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3682, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29353 p hg
    simpa only [d3682, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29397 (p : Pattern) (guard : d5850 p = 1) : d3683 p ≤ (0 : Int) + d2616 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3683, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29396 p hg
    simpa only [d3683, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3683, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3683, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29398 (p : Pattern) (guard : d5850 p = 1) : d3684 p ≤ (0 : Int) + d2617 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3684, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29390 p hg
    simpa only [d3684, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3684, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29397 p hg
    simpa only [d3684, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29399 (p : Pattern) (guard : d5850 p = 1) : d3685 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3685, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29378 p hg
    simpa only [d3685, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3685, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29391 p hg
    simpa only [d3685, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
