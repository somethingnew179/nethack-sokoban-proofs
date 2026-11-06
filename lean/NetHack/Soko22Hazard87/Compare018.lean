import NetHack.Soko22Hazard87.Compare017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4500 (p : Pattern) (guard : d39 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4501 (p : Pattern) (guard : d40 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4502 (p : Pattern) (guard : d41 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4501 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4503 (p : Pattern) (guard : d49 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4502 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4504 (p : Pattern) (guard : d50 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4503 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4505 (p : Pattern) (guard : d51 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d50 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4504 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4506 (p : Pattern) (guard : d52 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d51 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4507 (p : Pattern) (guard : d53 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d52 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4506 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4508 (p : Pattern) (guard : d54 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4507 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4509 (p : Pattern) (guard : d60 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d60, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54 p = 1 := by simpa only [d60, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4508 p hg
    simpa only [d60, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4510 (p : Pattern) (guard : d61 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4509 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4511 (p : Pattern) (guard : d62 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4510 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4512 (p : Pattern) (guard : d63 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d62 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4513 (p : Pattern) (guard : d64 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d63 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4512 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4514 (p : Pattern) (guard : d65 p = 1) : d47768 p ≤ (-1 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d59 p = 1 := by simpa only [d65, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d65, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64 p = 1 := by simpa only [d65, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4513 p hg
    simpa only [d65, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4515 (p : Pattern) (guard : d0 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4516 (p : Pattern) (guard : d0 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4517 (p : Pattern) (guard : d0 p = 1) : d47786 p ≤ (-1 : Int) + d47686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4518 (p : Pattern) (guard : d0 p = 1) : d47796 p ≤ (-1 : Int) + d47693 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4519 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4520 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare4521 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4522 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d15, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d15, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4523 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4524 (p : Pattern) (guard : d16 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4525 (p : Pattern) (guard : d17 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4524 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4526 (p : Pattern) (guard : d18 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4527 (p : Pattern) (guard : d19 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4528 (p : Pattern) (guard : d20 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4527 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4529 (p : Pattern) (guard : d21 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4528 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4530 (p : Pattern) (guard : d22 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4531 (p : Pattern) (guard : d0 p = 1) : d47631 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4532 (p : Pattern) (guard : d23 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4530 p hg
    simpa only [d23, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d23, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4533 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4534 (p : Pattern) (guard : d24 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4535 (p : Pattern) (guard : d66 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d66, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d24 p = 1 := by simpa only [d66, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d66, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4536 (p : Pattern) (guard : d25 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4419 p hg
    simpa only [d25, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d25, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4537 (p : Pattern) (guard : d67 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d66 p = 1 := by simpa only [d67, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4535 p hg
    simpa only [d67, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25 p = 1 := by simpa only [d67, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d67, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4538 (p : Pattern) (guard : d14 p = 1) : d6 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare4539 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4540 (p : Pattern) (guard : d15 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4538 p hg
    simpa only [d15, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d15, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4541 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4542 (p : Pattern) (guard : d16 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4543 (p : Pattern) (guard : d17 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4542 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4544 (p : Pattern) (guard : d18 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4543 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4545 (p : Pattern) (guard : d19 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4546 (p : Pattern) (guard : d20 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4545 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4547 (p : Pattern) (guard : d21 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4548 (p : Pattern) (guard : d22 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4547 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4549 (p : Pattern) (guard : d0 p = 1) : d47635 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4550 (p : Pattern) (guard : d23 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4548 p hg
    simpa only [d23, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d23, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4551 (p : Pattern) (guard : d0 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4552 (p : Pattern) (guard : d24 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4550 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4553 (p : Pattern) (guard : d25 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4552 p hg
    simpa only [d25, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d25, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4554 (p : Pattern) (guard : d26 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4553 p hg
    simpa only [d26, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d26, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4555 (p : Pattern) (guard : d68 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d67 p = 1 := by simpa only [d68, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4537 p hg
    simpa only [d68, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d68, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4554 p hg
    simpa only [d68, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4556 (p : Pattern) (guard : d0 p = 1) : d47802 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4557 (p : Pattern) (guard : d69 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d68 p = 1 := by simpa only [d69, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4555 p hg
    simpa only [d69, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d69, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d69, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4558 (p : Pattern) (guard : d0 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4559 (p : Pattern) (guard : d70 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d69 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4557 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4560 (p : Pattern) (guard : d71 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d70 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4559 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4561 (p : Pattern) (guard : d72 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d71 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4560 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4562 (p : Pattern) (guard : d73 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d73, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72 p = 1 := by simpa only [d73, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4561 p hg
    simpa only [d73, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4563 (p : Pattern) (guard : d74 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d74, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d74, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73 p = 1 := by simpa only [d74, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4562 p hg
    simpa only [d74, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4564 (p : Pattern) (guard : d0 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4565 (p : Pattern) (guard : d75 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d74 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4563 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4566 (p : Pattern) (guard : d76 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d75 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4565 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4567 (p : Pattern) (guard : d77 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d76 p = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4568 (p : Pattern) (guard : d0 p = 1) : d47806 p ≤ (-1 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4569 (p : Pattern) (guard : d78 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d77 p = 1 := by simpa only [d78, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4567 p hg
    simpa only [d78, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d78, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d78, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4570 (p : Pattern) (guard : d79 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d79, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d79, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d78 p = 1 := by simpa only [d79, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4569 p hg
    simpa only [d79, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4571 (p : Pattern) (guard : d80 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d79 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4570 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4572 (p : Pattern) (guard : d81 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d80 p = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4571 p hg
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4573 (p : Pattern) (guard : d82 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d81 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4574 (p : Pattern) (guard : d83 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d82 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4573 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4575 (p : Pattern) (guard : d84 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d83 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4574 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4576 (p : Pattern) (guard : d85 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d84 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4575 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4577 (p : Pattern) (guard : d86 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d85 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4576 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4578 (p : Pattern) (guard : d87 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d86 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4577 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4579 (p : Pattern) (guard : d88 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d87 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4580 (p : Pattern) (guard : d89 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d89, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d89, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d88 p = 1 := by simpa only [d89, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d89, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4581 (p : Pattern) (guard : d90 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d89 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4580 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4582 (p : Pattern) (guard : d91 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d90 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4581 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4583 (p : Pattern) (guard : d92 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d91 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4582 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4584 (p : Pattern) (guard : d93 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d92 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4583 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4585 (p : Pattern) (guard : d0 p = 1) : d47864 p ≤ (-1 : Int) + d98794 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4586 (p : Pattern) (guard : d94 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d93 p = 1 := by simpa only [d94, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4584 p hg
    simpa only [d94, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d94, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d94, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4587 (p : Pattern) (guard : d95 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65 p = 1 := by simpa only [d95, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4514 p hg
    simpa only [d95, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d94 p = 1 := by simpa only [d95, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4586 p hg
    simpa only [d95, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4588 (p : Pattern) (guard : d96 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d95 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4587 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4589 (p : Pattern) (guard : d97 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d96 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4588 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4590 (p : Pattern) (guard : d98 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d97 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4591 (p : Pattern) (guard : d99 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d98 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4590 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4592 (p : Pattern) (guard : d100 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4443 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4593 (p : Pattern) (guard : d101 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4592 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4594 (p : Pattern) (guard : d102 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4593 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4595 (p : Pattern) (guard : d103 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4594 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4596 (p : Pattern) (guard : d104 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4597 (p : Pattern) (guard : d105 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d104 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4596 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4598 (p : Pattern) (guard : d106 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d105 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4597 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4599 (p : Pattern) (guard : d107 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4450 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4600 (p : Pattern) (guard : d108 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4599 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4601 (p : Pattern) (guard : d109 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4600 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4602 (p : Pattern) (guard : d110 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4603 (p : Pattern) (guard : d111 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4604 (p : Pattern) (guard : d112 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d104 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4596 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4603 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4605 (p : Pattern) (guard : d113 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d112 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4604 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4606 (p : Pattern) (guard : d114 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d106 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4598 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d113 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4605 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4607 (p : Pattern) (guard : d115 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d40 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4440 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4608 (p : Pattern) (guard : d116 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d115 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4607 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4609 (p : Pattern) (guard : d117 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d116 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4608 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4610 (p : Pattern) (guard : d118 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d117 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4611 (p : Pattern) (guard : d119 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d118 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4612 (p : Pattern) (guard : d120 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d119 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4611 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4613 (p : Pattern) (guard : d121 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4439 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4614 (p : Pattern) (guard : d122 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d121 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4613 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4615 (p : Pattern) (guard : d123 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d122 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4614 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4616 (p : Pattern) (guard : d124 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d123 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4615 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4617 (p : Pattern) (guard : d125 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d124 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4618 (p : Pattern) (guard : d126 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d125 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4617 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4619 (p : Pattern) (guard : d128 p = 1) : d4 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare4620 (p : Pattern) (guard : d13 p = 1) : d4 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare4621 (p : Pattern) (guard : d14 p = 1) : d47616 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4622 (p : Pattern) (guard : d129 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4619 p hg
    simpa only [d129, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4621 p hg
    simpa only [d129, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4623 (p : Pattern) (guard : d130 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4622 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4407 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4624 (p : Pattern) (guard : d131 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4623 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4409 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4625 (p : Pattern) (guard : d132 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4624 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4410 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4626 (p : Pattern) (guard : d133 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4625 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4627 (p : Pattern) (guard : d134 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4626 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4628 (p : Pattern) (guard : d135 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4413 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4629 (p : Pattern) (guard : d136 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4414 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4630 (p : Pattern) (guard : d137 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4629 p hg
    simpa only [d137, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d137, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4631 (p : Pattern) (guard : d138 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4417 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4632 (p : Pattern) (guard : d139 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4631 p hg
    simpa only [d139, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d139, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4633 (p : Pattern) (guard : d140 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4632 p hg
    simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d140, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4634 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d141, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4633 p hg
    simpa only [d141, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4635 (p : Pattern) (guard : d142 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4634 p hg
    simpa only [d142, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d142, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4636 (p : Pattern) (guard : d143 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4635 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4425 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4637 (p : Pattern) (guard : d144 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4636 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4427 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4638 (p : Pattern) (guard : d145 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4428 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4639 (p : Pattern) (guard : d146 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d146, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4638 p hg
    simpa only [d146, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4640 (p : Pattern) (guard : d147 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d147, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4639 p hg
    simpa only [d147, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4641 (p : Pattern) (guard : d148 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4640 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4431 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4642 (p : Pattern) (guard : d149 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4641 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4433 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4643 (p : Pattern) (guard : d150 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4642 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4644 (p : Pattern) (guard : d151 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4643 p hg
    simpa only [d151, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d151, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4645 (p : Pattern) (guard : d152 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d152, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4644 p hg
    simpa only [d152, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4646 (p : Pattern) (guard : d153 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4645 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4438 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4647 (p : Pattern) (guard : d154 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4646 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4648 (p : Pattern) (guard : d155 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4647 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4649 (p : Pattern) (guard : d156 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4648 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4650 (p : Pattern) (guard : d157 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4649 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4442 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4651 (p : Pattern) (guard : d4335 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d157 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4650 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4652 (p : Pattern) (guard : d4336 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4335 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4651 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4653 (p : Pattern) (guard : d51641 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d126 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4618 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4336 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4652 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4654 (p : Pattern) (guard : d51642 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d120 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4612 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51641 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4655 (p : Pattern) (guard : d51643 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d51643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51642 p = 1 := by simpa only [d51643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4654 p hg
    simpa only [d51643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4656 (p : Pattern) (guard : d194 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d115 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4607 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4657 (p : Pattern) (guard : d195 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d194 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4656 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4658 (p : Pattern) (guard : d196 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d195 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4657 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4659 (p : Pattern) (guard : d197 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d196 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4658 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4660 (p : Pattern) (guard : d198 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d197 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4661 (p : Pattern) (guard : d199 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d122 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4614 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4662 (p : Pattern) (guard : d200 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d199 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4661 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4663 (p : Pattern) (guard : d201 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d200 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4664 (p : Pattern) (guard : d202 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d201 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4663 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4665 (p : Pattern) (guard : d203 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4648 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4666 (p : Pattern) (guard : d204 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4665 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4667 (p : Pattern) (guard : d4340 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d204 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4666 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4668 (p : Pattern) (guard : d4341 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4340 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4667 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4451 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4669 (p : Pattern) (guard : d51644 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d202 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4664 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4341 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4668 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4670 (p : Pattern) (guard : d51645 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d198 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4660 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51644 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4669 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4671 (p : Pattern) (guard : d51646 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51642 p = 1 := by simpa only [d51646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4654 p hg
    simpa only [d51646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51645 p = 1 := by simpa only [d51646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4670 p hg
    simpa only [d51646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4672 (p : Pattern) (guard : d51647 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51643 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4655 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51646 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4671 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4673 (p : Pattern) (guard : d213 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4674 (p : Pattern) (guard : d214 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d213 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4673 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4675 (p : Pattern) (guard : d51648 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51647 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4672 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d214 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4676 (p : Pattern) (guard : d51649 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51648 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4675 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4677 (p : Pattern) (guard : d51650 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d114 p = 1 := by simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4606 p hg
    simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51649 p = 1 := by simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4676 p hg
    simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4678 (p : Pattern) (guard : d128 p = 1) : d5 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare4679 (p : Pattern) (guard : d13 p = 1) : d5 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare4680 (p : Pattern) (guard : d14 p = 1) : d47705 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d14, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4681 (p : Pattern) (guard : d129 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d129, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4680 p hg
    simpa only [d129, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4682 (p : Pattern) (guard : d130 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4681 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4468 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4683 (p : Pattern) (guard : d131 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4684 (p : Pattern) (guard : d132 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4685 (p : Pattern) (guard : d133 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4684 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4686 (p : Pattern) (guard : d134 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4685 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4687 (p : Pattern) (guard : d135 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4686 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4474 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4688 (p : Pattern) (guard : d136 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4689 (p : Pattern) (guard : d137 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d137, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d137, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4690 (p : Pattern) (guard : d138 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4691 (p : Pattern) (guard : d139 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4690 p hg
    simpa only [d139, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d139, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4692 (p : Pattern) (guard : d140 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d140, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4693 (p : Pattern) (guard : d141 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d141, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4694 (p : Pattern) (guard : d142 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4693 p hg
    simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4695 (p : Pattern) (guard : d143 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4486 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4696 (p : Pattern) (guard : d144 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4697 (p : Pattern) (guard : d145 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4698 (p : Pattern) (guard : d146 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d146, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d146, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4699 (p : Pattern) (guard : d147 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d147, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d147, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4700 (p : Pattern) (guard : d148 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4492 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4701 (p : Pattern) (guard : d149 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4702 (p : Pattern) (guard : d150 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4701 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4703 (p : Pattern) (guard : d151 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4702 p hg
    simpa only [d151, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d151, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4704 (p : Pattern) (guard : d152 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d152, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4703 p hg
    simpa only [d152, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4705 (p : Pattern) (guard : d153 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4706 (p : Pattern) (guard : d154 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4705 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4707 (p : Pattern) (guard : d155 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4708 (p : Pattern) (guard : d203 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4709 (p : Pattern) (guard : d204 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4503 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4710 (p : Pattern) (guard : d4340 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d204 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4711 (p : Pattern) (guard : d4341 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4340 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4710 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4712 (p : Pattern) (guard : d4342 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4341 p = 1 := by simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4713 (p : Pattern) (guard : d4343 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4342 p = 1 := by simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4714 (p : Pattern) (guard : d4349 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4349, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4349, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4343 p = 1 := by simpa only [d4349, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d4349, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4715 (p : Pattern) (guard : d4350 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4349 p = 1 := by simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4714 p hg
    simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4716 (p : Pattern) (guard : d4351 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d4350 p = 1 := by simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4715 p hg
    simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4717 (p : Pattern) (guard : d4352 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d4351 p = 1 := by simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4716 p hg
    simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4718 (p : Pattern) (guard : d4353 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d4352 p = 1 := by simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4717 p hg
    simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4719 (p : Pattern) (guard : d51651 p = 1) : d47768 p ≤ (-1 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d51650 p = 1 := by simpa only [d51651, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4677 p hg
    simpa only [d51651, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4353 p = 1 := by simpa only [d51651, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4718 p hg
    simpa only [d51651, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4720 (p : Pattern) (guard : d128 p = 1) : d2 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare4721 (p : Pattern) (guard : d13 p = 1) : d2 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare4722 (p : Pattern) (guard : d14 p = 1) : d47629 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4721 p hg
    simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4723 (p : Pattern) (guard : d129 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d129, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4722 p hg
    simpa only [d129, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4724 (p : Pattern) (guard : d130 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4723 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4725 (p : Pattern) (guard : d131 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4724 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4524 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4726 (p : Pattern) (guard : d132 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4725 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4727 (p : Pattern) (guard : d133 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4726 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4728 (p : Pattern) (guard : d134 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4727 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4729 (p : Pattern) (guard : d135 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4728 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4528 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4730 (p : Pattern) (guard : d136 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4731 (p : Pattern) (guard : d137 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d137, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d137, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4732 (p : Pattern) (guard : d138 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4733 (p : Pattern) (guard : d226 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d226, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d226, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d138 p = 1 := by simpa only [d226, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d226, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4734 (p : Pattern) (guard : d139 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4631 p hg
    simpa only [d139, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d139, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4735 (p : Pattern) (guard : d227 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d226 p = 1 := by simpa only [d227, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d227, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d139 p = 1 := by simpa only [d227, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4734 p hg
    simpa only [d227, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4736 (p : Pattern) (guard : d128 p = 1) : d6 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare4737 (p : Pattern) (guard : d13 p = 1) : d6 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare4738 (p : Pattern) (guard : d14 p = 1) : d47633 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d14, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4739 (p : Pattern) (guard : d129 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4736 p hg
    simpa only [d129, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4738 p hg
    simpa only [d129, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4740 (p : Pattern) (guard : d130 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4739 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4741 (p : Pattern) (guard : d131 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4542 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4742 (p : Pattern) (guard : d132 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4543 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4743 (p : Pattern) (guard : d133 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4742 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4744 (p : Pattern) (guard : d134 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4745 (p : Pattern) (guard : d135 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4744 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4746 (p : Pattern) (guard : d136 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4547 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4747 (p : Pattern) (guard : d137 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4746 p hg
    simpa only [d137, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d137, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4748 (p : Pattern) (guard : d138 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4550 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4749 (p : Pattern) (guard : d139 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4748 p hg
    simpa only [d139, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d139, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
