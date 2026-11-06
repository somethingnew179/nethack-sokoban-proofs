import NetHack.Soko22Hazard87.Compare185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46500 (p : Pattern) (guard : d367200 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367199 p = 1 := by simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46499 p hg
    simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46501 (p : Pattern) (guard : d367201 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367196 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46496 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46502 (p : Pattern) (guard : d367202 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367201 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46501 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46503 (p : Pattern) (guard : d367203 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367202 p = 1 := by simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46502 p hg
    simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46504 (p : Pattern) (guard : d367204 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367203 p = 1 := by simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46503 p hg
    simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46505 (p : Pattern) (guard : d367205 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46500 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367204 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46504 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46506 (p : Pattern) (guard : d367206 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367205 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46505 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46507 (p : Pattern) (guard : d367207 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367206 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46506 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46508 (p : Pattern) (guard : d367221 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367207 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46507 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46509 (p : Pattern) (guard : d367209 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367204 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46504 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46510 (p : Pattern) (guard : d367210 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367209 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46509 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46511 (p : Pattern) (guard : d367211 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367210 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46510 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46512 (p : Pattern) (guard : d367222 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367211 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46511 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46513 (p : Pattern) (guard : d367223 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367221 p = 1 := by simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46508 p hg
    simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367222 p = 1 := by simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46512 p hg
    simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46514 (p : Pattern) (guard : d367224 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367223 p = 1 := by simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46513 p hg
    simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46515 (p : Pattern) (guard : d367225 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367224 p = 1 := by simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46514 p hg
    simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46516 (p : Pattern) (guard : d367226 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367225 p = 1 := by simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46517 (p : Pattern) (guard : d367227 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367226 p = 1 := by simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46516 p hg
    simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46518 (p : Pattern) (guard : d367528 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367528, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367528, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367227 p = 1 := by simpa only [d367528, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46517 p hg
    simpa only [d367528, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46519 (p : Pattern) (guard : d367529 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367528 p = 1 := by simpa only [d367529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46518 p hg
    simpa only [d367529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46520 (p : Pattern) (guard : d367530 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367529 p = 1 := by simpa only [d367530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46519 p hg
    simpa only [d367530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46521 (p : Pattern) (guard : d367531 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367530 p = 1 := by simpa only [d367531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46520 p hg
    simpa only [d367531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46522 (p : Pattern) (guard : d367532 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367531 p = 1 := by simpa only [d367532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46521 p hg
    simpa only [d367532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46523 (p : Pattern) (guard : d367533 p = 1) : d51470 p ≤ (7 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367527 p = 1 := by simpa only [d367533, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46476 p hg
    simpa only [d367533, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367532 p = 1 := by simpa only [d367533, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46522 p hg
    simpa only [d367533, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46524 (p : Pattern) (guard : d35372 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32698 p = 1 := by simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46293 p hg
    simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46525 (p : Pattern) (guard : d2006 p = 1) : d51183 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45701 p hg
    simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46295 p hg
    simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46526 (p : Pattern) (guard : d10054 p = 1) : d51186 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46525 p hg
    simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46297 p hg
    simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46527 (p : Pattern) (guard : d10055 p = 1) : d51186 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46526 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46528 (p : Pattern) (guard : d35373 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d35372 p = 1 := by simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46524 p hg
    simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46527 p hg
    simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46529 (p : Pattern) (guard : d44441 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d35373 p = 1 := by simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46528 p hg
    simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46530 (p : Pattern) (guard : d44442 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d44441 p = 1 := by simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46529 p hg
    simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46531 (p : Pattern) (guard : d44443 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d44442 p = 1 := by simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46530 p hg
    simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46532 (p : Pattern) (guard : d44444 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45397 p hg
    simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44443 p = 1 := by simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46531 p hg
    simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46533 (p : Pattern) (guard : d44686 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44444 p = 1 := by simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46532 p hg
    simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46534 (p : Pattern) (guard : d44445 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d44444 p = 1 := by simpa only [d44445, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46404 p hg
    simpa only [d44445, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44445, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d44445, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46535 (p : Pattern) (guard : d44687 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d44686 p = 1 := by simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46533 p hg
    simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44445 p = 1 := by simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46534 p hg
    simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46536 (p : Pattern) (guard : d44446 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46537 (p : Pattern) (guard : d44688 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d44687 p = 1 := by simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46535 p hg
    simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44446 p = 1 := by simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46536 p hg
    simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46538 (p : Pattern) (guard : d44689 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44688 p = 1 := by simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46537 p hg
    simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46539 (p : Pattern) (guard : d44690 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44689 p = 1 := by simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46538 p hg
    simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46540 (p : Pattern) (guard : d44609 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d44443 p = 1 := by simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46531 p hg
    simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45397 p hg
    simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46541 (p : Pattern) (guard : d44784 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44609 p = 1 := by simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46540 p hg
    simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46542 (p : Pattern) (guard : d44610 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d44609 p = 1 := by simpa only [d44610, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46410 p hg
    simpa only [d44610, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44610, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d44610, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46543 (p : Pattern) (guard : d44785 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d44784 p = 1 := by simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46541 p hg
    simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44610 p = 1 := by simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46542 p hg
    simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46544 (p : Pattern) (guard : d44611 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46545 (p : Pattern) (guard : d44786 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d44785 p = 1 := by simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46543 p hg
    simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44611 p = 1 := by simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46544 p hg
    simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46546 (p : Pattern) (guard : d44787 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44786 p = 1 := by simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46545 p hg
    simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46547 (p : Pattern) (guard : d367321 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44689 p = 1 := by simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46538 p hg
    simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44787 p = 1 := by simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46546 p hg
    simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46548 (p : Pattern) (guard : d367322 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44690 p = 1 := by simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46539 p hg
    simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367321 p = 1 := by simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46547 p hg
    simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46549 (p : Pattern) (guard : d44788 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44787 p = 1 := by simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46546 p hg
    simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46550 (p : Pattern) (guard : d367326 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367321 p = 1 := by simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46547 p hg
    simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44788 p = 1 := by simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46549 p hg
    simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46551 (p : Pattern) (guard : d367327 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367322 p = 1 := by simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46548 p hg
    simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367326 p = 1 := by simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46550 p hg
    simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46552 (p : Pattern) (guard : d367328 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367327 p = 1 := by simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46551 p hg
    simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46553 (p : Pattern) (guard : d367329 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367328 p = 1 := by simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46552 p hg
    simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46554 (p : Pattern) (guard : d44790 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44788 p = 1 := by simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46549 p hg
    simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46555 (p : Pattern) (guard : d367331 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367326 p = 1 := by simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46550 p hg
    simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44790 p = 1 := by simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46554 p hg
    simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46556 (p : Pattern) (guard : d367332 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367331 p = 1 := by simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46555 p hg
    simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46557 (p : Pattern) (guard : d367333 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367332 p = 1 := by simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46556 p hg
    simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46558 (p : Pattern) (guard : d367334 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367329 p = 1 := by simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46553 p hg
    simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367333 p = 1 := by simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46557 p hg
    simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46559 (p : Pattern) (guard : d367339 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367333 p = 1 := by simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46557 p hg
    simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46560 (p : Pattern) (guard : d367340 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367334 p = 1 := by simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46558 p hg
    simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367339 p = 1 := by simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46559 p hg
    simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46561 (p : Pattern) (guard : d367341 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367340 p = 1 := by simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46560 p hg
    simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46562 (p : Pattern) (guard : d367342 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367341 p = 1 := by simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46561 p hg
    simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46563 (p : Pattern) (guard : d367343 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367342 p = 1 := by simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46562 p hg
    simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46564 (p : Pattern) (guard : d367348 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367339 p = 1 := by simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46559 p hg
    simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46565 (p : Pattern) (guard : d367349 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367348 p = 1 := by simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46564 p hg
    simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46566 (p : Pattern) (guard : d367350 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367349 p = 1 := by simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46565 p hg
    simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46567 (p : Pattern) (guard : d367351 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367350 p = 1 := by simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46566 p hg
    simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46568 (p : Pattern) (guard : d367352 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367343 p = 1 := by simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46563 p hg
    simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367351 p = 1 := by simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46567 p hg
    simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46569 (p : Pattern) (guard : d367353 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367352 p = 1 := by simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46568 p hg
    simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46570 (p : Pattern) (guard : d367354 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367353 p = 1 := by simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46569 p hg
    simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46571 (p : Pattern) (guard : d367355 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367354 p = 1 := by simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46570 p hg
    simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46572 (p : Pattern) (guard : d367369 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367351 p = 1 := by simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46567 p hg
    simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46573 (p : Pattern) (guard : d367370 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367369 p = 1 := by simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46572 p hg
    simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46574 (p : Pattern) (guard : d367371 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367370 p = 1 := by simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46573 p hg
    simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46575 (p : Pattern) (guard : d367372 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367371 p = 1 := by simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46574 p hg
    simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46576 (p : Pattern) (guard : d367534 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367355 p = 1 := by simpa only [d367534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46571 p hg
    simpa only [d367534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367372 p = 1 := by simpa only [d367534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46575 p hg
    simpa only [d367534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46577 (p : Pattern) (guard : d367535 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367534 p = 1 := by simpa only [d367535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46576 p hg
    simpa only [d367535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46578 (p : Pattern) (guard : d367536 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367535 p = 1 := by simpa only [d367536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46577 p hg
    simpa only [d367536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46579 (p : Pattern) (guard : d367537 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367536 p = 1 := by simpa only [d367537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46578 p hg
    simpa only [d367537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46580 (p : Pattern) (guard : d367538 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367537 p = 1 := by simpa only [d367538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46579 p hg
    simpa only [d367538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46581 (p : Pattern) (guard : d367539 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367539, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367539, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367538 p = 1 := by simpa only [d367539, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46580 p hg
    simpa only [d367539, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46582 (p : Pattern) (guard : d367540 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367539 p = 1 := by simpa only [d367540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46581 p hg
    simpa only [d367540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46583 (p : Pattern) (guard : d367541 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367540 p = 1 := by simpa only [d367541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46582 p hg
    simpa only [d367541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46584 (p : Pattern) (guard : d367542 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367541 p = 1 := by simpa only [d367542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46583 p hg
    simpa only [d367542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46585 (p : Pattern) (guard : d367543 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367542 p = 1 := by simpa only [d367543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46584 p hg
    simpa only [d367543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46586 (p : Pattern) (guard : d367544 p = 1) : d51634 p ≤ (7 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367543 p = 1 := by simpa only [d367544, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46585 p hg
    simpa only [d367544, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367544, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d367544, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46587 (p : Pattern) (guard : d367545 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d367533 p = 1 := by simpa only [d367545, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46523 p hg
    simpa only [d367545, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367544 p = 1 := by simpa only [d367545, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46586 p hg
    simpa only [d367545, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46588 (p : Pattern) (guard : d367546 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367545 p = 1 := by simpa only [d367546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46587 p hg
    simpa only [d367546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46589 (p : Pattern) (guard : d367547 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367546 p = 1 := by simpa only [d367547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46588 p hg
    simpa only [d367547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46590 (p : Pattern) (guard : d367548 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367547 p = 1 := by simpa only [d367548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46589 p hg
    simpa only [d367548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46591 (p : Pattern) (guard : d367549 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367548 p = 1 := by simpa only [d367549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46590 p hg
    simpa only [d367549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46592 (p : Pattern) (guard : d367550 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367549 p = 1 := by simpa only [d367550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46591 p hg
    simpa only [d367550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46593 (p : Pattern) (guard : d367551 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367550 p = 1 := by simpa only [d367551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46592 p hg
    simpa only [d367551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46594 (p : Pattern) (guard : d367552 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367551 p = 1 := by simpa only [d367552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46593 p hg
    simpa only [d367552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46595 (p : Pattern) (guard : d367553 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367552 p = 1 := by simpa only [d367553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46594 p hg
    simpa only [d367553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46596 (p : Pattern) (guard : d367554 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367553 p = 1 := by simpa only [d367554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46595 p hg
    simpa only [d367554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46597 (p : Pattern) (guard : d367555 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367554 p = 1 := by simpa only [d367555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46596 p hg
    simpa only [d367555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46598 (p : Pattern) (guard : d367556 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d367525 p = 1 := by simpa only [d367556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46395 p hg
    simpa only [d367556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367555 p = 1 := by simpa only [d367556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46597 p hg
    simpa only [d367556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46599 (p : Pattern) (guard : d367557 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 260 with
  | false =>
    have hg : d367556 p = 1 := by simpa only [d367557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46598 p hg
    simpa only [d367557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46600 (p : Pattern) (guard : d367558 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 259 with
  | false =>
    have hg : d367557 p = 1 := by simpa only [d367558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46599 p hg
    simpa only [d367558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46601 (p : Pattern) (guard : d367559 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 258 with
  | false =>
    have hg : d367558 p = 1 := by simpa only [d367559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46600 p hg
    simpa only [d367559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46602 (p : Pattern) (guard : d367560 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 257 with
  | false =>
    have hg : d367559 p = 1 := by simpa only [d367560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46601 p hg
    simpa only [d367560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46603 (p : Pattern) (guard : d367561 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 256 with
  | false =>
    have hg : d367560 p = 1 := by simpa only [d367561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46602 p hg
    simpa only [d367561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46604 (p : Pattern) (guard : d367562 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 255 with
  | false =>
    have hg : d367561 p = 1 := by simpa only [d367562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46603 p hg
    simpa only [d367562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46605 (p : Pattern) (guard : d367563 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 254 with
  | false =>
    have hg : d367562 p = 1 := by simpa only [d367563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46604 p hg
    simpa only [d367563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46606 (p : Pattern) (guard : d367564 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 253 with
  | false =>
    have hg : d367563 p = 1 := by simpa only [d367564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46605 p hg
    simpa only [d367564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46607 (p : Pattern) (guard : d367565 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 252 with
  | false =>
    have hg : d367564 p = 1 := by simpa only [d367565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46606 p hg
    simpa only [d367565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46608 (p : Pattern) (guard : d367566 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 251 with
  | false =>
    have hg : d367565 p = 1 := by simpa only [d367566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46607 p hg
    simpa only [d367566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46609 (p : Pattern) (guard : d367567 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 250 with
  | false =>
    have hg : d367566 p = 1 := by simpa only [d367567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46608 p hg
    simpa only [d367567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46610 (p : Pattern) (guard : d367568 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 249 with
  | false =>
    have hg : d367567 p = 1 := by simpa only [d367568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46609 p hg
    simpa only [d367568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46611 (p : Pattern) (guard : d367569 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 245 with
  | false =>
    have hg : d367568 p = 1 := by simpa only [d367569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46610 p hg
    simpa only [d367569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46612 (p : Pattern) (guard : d367570 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 200 with
  | false =>
    have hg : d367569 p = 1 := by simpa only [d367570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46611 p hg
    simpa only [d367570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46613 (p : Pattern) (guard : d367571 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 199 with
  | false =>
    have hg : d367570 p = 1 := by simpa only [d367571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46612 p hg
    simpa only [d367571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46614 (p : Pattern) (guard : d367572 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 186 with
  | false =>
    have hg : d367571 p = 1 := by simpa only [d367572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46613 p hg
    simpa only [d367572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46615 (p : Pattern) (guard : d367573 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 185 with
  | false =>
    have hg : d367572 p = 1 := by simpa only [d367573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46614 p hg
    simpa only [d367573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46616 (p : Pattern) (guard : d367574 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 184 with
  | false =>
    have hg : d367573 p = 1 := by simpa only [d367574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46615 p hg
    simpa only [d367574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46617 (p : Pattern) (guard : d367575 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 181 with
  | false =>
    have hg : d367574 p = 1 := by simpa only [d367575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46616 p hg
    simpa only [d367575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46618 (p : Pattern) (guard : d367576 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 177 with
  | false =>
    have hg : d367575 p = 1 := by simpa only [d367576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46617 p hg
    simpa only [d367576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46619 (p : Pattern) (guard : d367577 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 164 with
  | false =>
    have hg : d367576 p = 1 := by simpa only [d367577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46618 p hg
    simpa only [d367577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46620 (p : Pattern) (guard : d367578 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 156 with
  | false =>
    have hg : d367577 p = 1 := by simpa only [d367578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46619 p hg
    simpa only [d367578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46621 (p : Pattern) (guard : d367579 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 155 with
  | false =>
    have hg : d367578 p = 1 := by simpa only [d367579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46620 p hg
    simpa only [d367579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46622 (p : Pattern) (guard : d367580 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 134 with
  | false =>
    have hg : d367579 p = 1 := by simpa only [d367580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46621 p hg
    simpa only [d367580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46623 (p : Pattern) (guard : d367581 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 133 with
  | false =>
    have hg : d367580 p = 1 := by simpa only [d367581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46622 p hg
    simpa only [d367581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46624 (p : Pattern) (guard : d367582 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 120 with
  | false =>
    have hg : d367581 p = 1 := by simpa only [d367582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46623 p hg
    simpa only [d367582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46625 (p : Pattern) (guard : d367583 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 118 with
  | false =>
    have hg : d367582 p = 1 := by simpa only [d367583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46624 p hg
    simpa only [d367583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46626 (p : Pattern) (guard : d367584 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 114 with
  | false =>
    have hg : d367583 p = 1 := by simpa only [d367584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46625 p hg
    simpa only [d367584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46627 (p : Pattern) (guard : d367585 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 111 with
  | false =>
    have hg : d367584 p = 1 := by simpa only [d367585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46626 p hg
    simpa only [d367585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46628 (p : Pattern) (guard : d367586 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 98 with
  | false =>
    have hg : d367585 p = 1 := by simpa only [d367586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46627 p hg
    simpa only [d367586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46629 (p : Pattern) (guard : d367587 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 97 with
  | false =>
    have hg : d367586 p = 1 := by simpa only [d367587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46628 p hg
    simpa only [d367587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46630 (p : Pattern) (guard : d367588 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 94 with
  | false =>
    have hg : d367587 p = 1 := by simpa only [d367588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46629 p hg
    simpa only [d367588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46631 (p : Pattern) (guard : d367589 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 76 with
  | false =>
    have hg : d367588 p = 1 := by simpa only [d367589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46630 p hg
    simpa only [d367589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46632 (p : Pattern) (guard : d367590 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 67 with
  | false =>
    have hg : d367589 p = 1 := by simpa only [d367590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46631 p hg
    simpa only [d367590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46633 (p : Pattern) (guard : d367591 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 52 with
  | false =>
    have hg : d367590 p = 1 := by simpa only [d367591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46632 p hg
    simpa only [d367591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46634 (p : Pattern) (guard : d367592 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 47 with
  | false =>
    have hg : d367591 p = 1 := by simpa only [d367592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46633 p hg
    simpa only [d367592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46635 (p : Pattern) (guard : d367593 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 46 with
  | false =>
    have hg : d367592 p = 1 := by simpa only [d367593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46634 p hg
    simpa only [d367593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46636 (p : Pattern) (guard : d367594 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 45 with
  | false =>
    have hg : d367593 p = 1 := by simpa only [d367594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46635 p hg
    simpa only [d367594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46637 (p : Pattern) (guard : d367595 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 30 with
  | false =>
    have hg : d367594 p = 1 := by simpa only [d367595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46636 p hg
    simpa only [d367595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46638 (p : Pattern) (guard : d367596 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 29 with
  | false =>
    have hg : d367595 p = 1 := by simpa only [d367596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46637 p hg
    simpa only [d367596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46639 (p : Pattern) (guard : d367597 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 28 with
  | false =>
    have hg : d367596 p = 1 := by simpa only [d367597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46638 p hg
    simpa only [d367597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46640 (p : Pattern) (guard : d367598 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 27 with
  | false =>
    have hg : d367597 p = 1 := by simpa only [d367598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46639 p hg
    simpa only [d367598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46641 (p : Pattern) (guard : d367599 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 25 with
  | false =>
    have hg : d367598 p = 1 := by simpa only [d367599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46640 p hg
    simpa only [d367599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46642 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-1 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46643 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-2 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46644 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46645 (p : Pattern) (guard : d0 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46646 (p : Pattern) (guard : d0 p = 1) : d50588 p ≤ (1 : Int) + d367817 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46647 (p : Pattern) (guard : d0 p = 1) : d50546 p ≤ (1 : Int) + d367788 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46648 (p : Pattern) (guard : d0 p = 1) : d50566 p ≤ (1 : Int) + d367798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46649 (p : Pattern) (guard : d0 p = 1) : d50569 p ≤ (1 : Int) + d367800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46650 (p : Pattern) (guard : d45587 p = 1) : d47617 p ≤ (1 : Int) + d47617 p := by
  omega
theorem compare46651 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (1 : Int) + d49391 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46652 (p : Pattern) (guard : d46472 p = 1) : d47617 p ≤ (1 : Int) + d49392 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46650 p hg
    simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46651 p hg
    simpa only [d46472, d49392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46653 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (1 : Int) + d49395 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46654 (p : Pattern) (guard : d46473 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46652 p hg
    simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46653 p hg
    simpa only [d46473, d49396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46655 (p : Pattern) (guard : d46477 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46654 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46656 (p : Pattern) (guard : d0 p = 1) : d49396 p ≤ (1 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46657 (p : Pattern) (guard : d179204 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46655 p hg
    simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46656 p hg
    simpa only [d179204, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46658 (p : Pattern) (guard : d275501 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46657 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46659 (p : Pattern) (guard : d275502 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46658 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46660 (p : Pattern) (guard : d0 p = 1) : d49397 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46661 (p : Pattern) (guard : d275503 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46659 p hg
    simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d275503, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46662 (p : Pattern) (guard : d0 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46663 (p : Pattern) (guard : d275504 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46661 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46662 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46664 (p : Pattern) (guard : d0 p = 1) : d50527 p ≤ (1 : Int) + d367774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46665 (p : Pattern) (guard : d275505 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46663 p hg
    simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d275505, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46666 (p : Pattern) (guard : d0 p = 1) : d50531 p ≤ (1 : Int) + d367777 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46667 (p : Pattern) (guard : d275506 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275505 p = 1 := by simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46665 p hg
    simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d275506, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46668 (p : Pattern) (guard : d275507 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275506 p = 1 := by simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46667 p hg
    simpa only [d275507, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46669 (p : Pattern) (guard : d0 p = 1) : d50575 p ≤ (1 : Int) + d367804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46670 (p : Pattern) (guard : d275508 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d275507 p = 1 := by simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46668 p hg
    simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d275508, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46671 (p : Pattern) (guard : d0 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46672 (p : Pattern) (guard : d275509 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d275508 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46670 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46671 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46673 (p : Pattern) (guard : d275510 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d275509 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46671 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46674 (p : Pattern) (guard : d275511 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d275510 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46673 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46671 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46675 (p : Pattern) (guard : d275512 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275511 p = 1 := by simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46674 p hg
    simpa only [d275512, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46676 (p : Pattern) (guard : d275513 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275512 p = 1 := by simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46675 p hg
    simpa only [d275513, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46677 (p : Pattern) (guard : d0 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46678 (p : Pattern) (guard : d275514 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d275513 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46676 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46679 (p : Pattern) (guard : d275515 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d275514 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46678 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46680 (p : Pattern) (guard : d275516 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d275515 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46679 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46681 (p : Pattern) (guard : d0 p = 1) : d50589 p ≤ (1 : Int) + d367818 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46682 (p : Pattern) (guard : d275517 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d275516 p = 1 := by simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46680 p hg
    simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d275517, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46683 (p : Pattern) (guard : d275518 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275517 p = 1 := by simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46682 p hg
    simpa only [d275518, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46684 (p : Pattern) (guard : d275519 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d275518 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46683 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46685 (p : Pattern) (guard : d275520 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d275519 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46684 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46686 (p : Pattern) (guard : d275521 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d275520 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46685 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46687 (p : Pattern) (guard : d275522 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275521 p = 1 := by simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46686 p hg
    simpa only [d275522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46688 (p : Pattern) (guard : d275523 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275522 p = 1 := by simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46687 p hg
    simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46689 (p : Pattern) (guard : d275524 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d275523 p = 1 := by simpa only [d275524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46688 p hg
    simpa only [d275524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46690 (p : Pattern) (guard : d275525 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275524 p = 1 := by simpa only [d275525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46689 p hg
    simpa only [d275525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46691 (p : Pattern) (guard : d275526 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275525 p = 1 := by simpa only [d275526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46690 p hg
    simpa only [d275526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46692 (p : Pattern) (guard : d275527 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275526 p = 1 := by simpa only [d275527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46691 p hg
    simpa only [d275527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46693 (p : Pattern) (guard : d275528 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275527 p = 1 := by simpa only [d275528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46692 p hg
    simpa only [d275528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46694 (p : Pattern) (guard : d275529 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275521 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46686 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46695 (p : Pattern) (guard : d275530 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275529 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46694 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46696 (p : Pattern) (guard : d275531 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d275530 p = 1 := by simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46695 p hg
    simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46697 (p : Pattern) (guard : d275532 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275531 p = 1 := by simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46696 p hg
    simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46698 (p : Pattern) (guard : d275533 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275532 p = 1 := by simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46697 p hg
    simpa only [d275533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46699 (p : Pattern) (guard : d275534 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275533 p = 1 := by simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46698 p hg
    simpa only [d275534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46700 (p : Pattern) (guard : d275535 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d275527 p = 1 := by simpa only [d275535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46692 p hg
    simpa only [d275535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275534 p = 1 := by simpa only [d275535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46699 p hg
    simpa only [d275535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46701 (p : Pattern) (guard : d275536 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d275528 p = 1 := by simpa only [d275536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46693 p hg
    simpa only [d275536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275535 p = 1 := by simpa only [d275536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46700 p hg
    simpa only [d275536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46702 (p : Pattern) (guard : d275537 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d275536 p = 1 := by simpa only [d275537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46701 p hg
    simpa only [d275537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46703 (p : Pattern) (guard : d275538 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d275537 p = 1 := by simpa only [d275538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46702 p hg
    simpa only [d275538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46704 (p : Pattern) (guard : d275539 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275538 p = 1 := by simpa only [d275539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46703 p hg
    simpa only [d275539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46705 (p : Pattern) (guard : d0 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46706 (p : Pattern) (guard : d0 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46707 (p : Pattern) (guard : d0 p = 1) : d50671 p ≤ (1 : Int) + d367875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46708 (p : Pattern) (guard : d0 p = 1) : d50631 p ≤ (1 : Int) + d367850 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46709 (p : Pattern) (guard : d0 p = 1) : d50653 p ≤ (1 : Int) + d367860 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46710 (p : Pattern) (guard : d0 p = 1) : d50656 p ≤ (1 : Int) + d367862 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46711 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (1 : Int) + d47706 p := by
  omega
theorem compare46712 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (1 : Int) + d49560 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46713 (p : Pattern) (guard : d46472 p = 1) : d47706 p ≤ (1 : Int) + d49561 p := by
  cases selected : p 225 with
  | false =>
    have hg : d45587 p = 1 := by simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46711 p hg
    simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46712 p hg
    simpa only [d46472, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46714 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (1 : Int) + d49564 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46715 (p : Pattern) (guard : d46473 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46472 p = 1 := by simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46713 p hg
    simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46714 p hg
    simpa only [d46473, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46716 (p : Pattern) (guard : d46477 p = 1) : d47706 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46473 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46715 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d46477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46717 (p : Pattern) (guard : d0 p = 1) : d49565 p ≤ (1 : Int) + d49565 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46718 (p : Pattern) (guard : d179204 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46477 p = 1 := by simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46716 p hg
    simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46717 p hg
    simpa only [d179204, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46719 (p : Pattern) (guard : d275501 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d179204 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46718 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d275501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46720 (p : Pattern) (guard : d275502 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d275501 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46719 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d275502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46721 (p : Pattern) (guard : d0 p = 1) : d49566 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46722 (p : Pattern) (guard : d275503 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d275502 p = 1 := by simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46720 p hg
    simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d275503, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46723 (p : Pattern) (guard : d0 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46724 (p : Pattern) (guard : d275504 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d275503 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46722 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46723 p hg
    simpa only [d275504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46725 (p : Pattern) (guard : d0 p = 1) : d50530 p ≤ (1 : Int) + d367776 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46726 (p : Pattern) (guard : d275505 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d275504 p = 1 := by simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46724 p hg
    simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d275505, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46727 (p : Pattern) (guard : d275506 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d275505 p = 1 := by simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46726 p hg
    simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d275506, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46728 (p : Pattern) (guard : d275507 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275506 p = 1 := by simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46727 p hg
    simpa only [d275507, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46729 (p : Pattern) (guard : d0 p = 1) : d50662 p ≤ (1 : Int) + d367866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46730 (p : Pattern) (guard : d275508 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d275507 p = 1 := by simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46728 p hg
    simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d275508, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46731 (p : Pattern) (guard : d0 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46732 (p : Pattern) (guard : d275509 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d275508 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46730 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46731 p hg
    simpa only [d275509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46733 (p : Pattern) (guard : d275510 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d275509 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46732 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46731 p hg
    simpa only [d275510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46734 (p : Pattern) (guard : d275511 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d275510 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46733 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46731 p hg
    simpa only [d275511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46735 (p : Pattern) (guard : d275512 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275511 p = 1 := by simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46734 p hg
    simpa only [d275512, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46736 (p : Pattern) (guard : d275513 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275512 p = 1 := by simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46735 p hg
    simpa only [d275513, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46737 (p : Pattern) (guard : d0 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46738 (p : Pattern) (guard : d275514 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d275513 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46736 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d275514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46739 (p : Pattern) (guard : d275515 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d275514 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46738 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d275515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46740 (p : Pattern) (guard : d275516 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d275515 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46739 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d275516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46741 (p : Pattern) (guard : d0 p = 1) : d50672 p ≤ (1 : Int) + d367876 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46742 (p : Pattern) (guard : d275517 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d275516 p = 1 := by simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46740 p hg
    simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d275517, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46743 (p : Pattern) (guard : d275518 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275517 p = 1 := by simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46742 p hg
    simpa only [d275518, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46744 (p : Pattern) (guard : d275519 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d275518 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46743 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46745 (p : Pattern) (guard : d275520 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d275519 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46744 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46746 (p : Pattern) (guard : d275521 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d275520 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46745 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46747 (p : Pattern) (guard : d275529 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d275521 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46746 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46748 (p : Pattern) (guard : d275530 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d275529 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46747 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46749 (p : Pattern) (guard : d275531 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d275530 p = 1 := by simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46748 p hg
    simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d275531, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
