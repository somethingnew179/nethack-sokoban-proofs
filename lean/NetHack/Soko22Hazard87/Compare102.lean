import NetHack.Soko22Hazard87.Compare101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25500 (p : Pattern) (guard : d0 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25501 (p : Pattern) (guard : d16 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25499 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25502 (p : Pattern) (guard : d17 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25501 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25503 (p : Pattern) (guard : d18 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25502 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25504 (p : Pattern) (guard : d19 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25503 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25505 (p : Pattern) (guard : d20 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25504 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25506 (p : Pattern) (guard : d21 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25505 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25507 (p : Pattern) (guard : d22 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25506 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25508 (p : Pattern) (guard : d0 p = 1) : d47614 p ≤ (-1 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25509 (p : Pattern) (guard : d23 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25507 p hg
    simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d23, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25510 (p : Pattern) (guard : d0 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25511 (p : Pattern) (guard : d24 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25512 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25513 (p : Pattern) (guard : d25 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25511 p hg
    simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d25, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25514 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (-1 : Int) + d47793 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25515 (p : Pattern) (guard : d26 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25513 p hg
    simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d26, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25516 (p : Pattern) (guard : d27 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25515 p hg
    simpa only [d27, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25517 (p : Pattern) (guard : d0 p = 1) : d48568 p ≤ (-1 : Int) + d48498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25518 (p : Pattern) (guard : d28 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25516 p hg
    simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d28, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25519 (p : Pattern) (guard : d29 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25518 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25520 (p : Pattern) (guard : d30 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25519 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25521 (p : Pattern) (guard : d31 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25520 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25522 (p : Pattern) (guard : d18544 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d31 p = 1 := by simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25521 p hg
    simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18544, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25523 (p : Pattern) (guard : d18545 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18544 p = 1 := by simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25522 p hg
    simpa only [d18545, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25524 (p : Pattern) (guard : d18546 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18545 p = 1 := by simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25523 p hg
    simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d18546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25525 (p : Pattern) (guard : d18547 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18546 p = 1 := by simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25524 p hg
    simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d18547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25526 (p : Pattern) (guard : d187879 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25495 p hg
    simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18547 p = 1 := by simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25525 p hg
    simpa only [d187879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25527 (p : Pattern) (guard : d0 p = 1) : d48704 p ≤ (-1 : Int) + d188505 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25528 (p : Pattern) (guard : d187880 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187879 p = 1 := by simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25526 p hg
    simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d187880, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25529 (p : Pattern) (guard : d187881 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187880 p = 1 := by simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25528 p hg
    simpa only [d187881, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25530 (p : Pattern) (guard : d187882 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187881 p = 1 := by simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25529 p hg
    simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25531 (p : Pattern) (guard : d187883 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187882 p = 1 := by simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25530 p hg
    simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25532 (p : Pattern) (guard : d187884 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187883 p = 1 := by simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25531 p hg
    simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25533 (p : Pattern) (guard : d187885 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187884 p = 1 := by simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25532 p hg
    simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25534 (p : Pattern) (guard : d187886 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187885 p = 1 := by simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25533 p hg
    simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25535 (p : Pattern) (guard : d187887 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d187886 p = 1 := by simpa only [d187887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25534 p hg
    simpa only [d187887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25536 (p : Pattern) (guard : d187888 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d187887 p = 1 := by simpa only [d187888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25535 p hg
    simpa only [d187888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25537 (p : Pattern) (guard : d187889 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187888 p = 1 := by simpa only [d187889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25536 p hg
    simpa only [d187889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25538 (p : Pattern) (guard : d187890 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187889 p = 1 := by simpa only [d187890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25537 p hg
    simpa only [d187890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25539 (p : Pattern) (guard : d187891 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187891, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d187891, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187890 p = 1 := by simpa only [d187891, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25538 p hg
    simpa only [d187891, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25540 (p : Pattern) (guard : d187892 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187891 p = 1 := by simpa only [d187892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25539 p hg
    simpa only [d187892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25541 (p : Pattern) (guard : d187893 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d187892 p = 1 := by simpa only [d187893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25540 p hg
    simpa only [d187893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25542 (p : Pattern) (guard : d187894 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d187893 p = 1 := by simpa only [d187894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25541 p hg
    simpa only [d187894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25543 (p : Pattern) (guard : d187895 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d187894 p = 1 := by simpa only [d187895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25542 p hg
    simpa only [d187895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25544 (p : Pattern) (guard : d0 p = 1) : d48747 p ≤ (-1 : Int) + d188516 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25545 (p : Pattern) (guard : d187896 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d187895 p = 1 := by simpa only [d187896, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25543 p hg
    simpa only [d187896, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187896, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d187896, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25546 (p : Pattern) (guard : d187897 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187897, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d187897, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187896 p = 1 := by simpa only [d187897, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25545 p hg
    simpa only [d187897, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25547 (p : Pattern) (guard : d187898 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187897 p = 1 := by simpa only [d187898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25546 p hg
    simpa only [d187898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25548 (p : Pattern) (guard : d187899 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187898 p = 1 := by simpa only [d187899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25547 p hg
    simpa only [d187899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25549 (p : Pattern) (guard : d187900 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187899 p = 1 := by simpa only [d187900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25548 p hg
    simpa only [d187900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25550 (p : Pattern) (guard : d187901 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187900 p = 1 := by simpa only [d187901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25549 p hg
    simpa only [d187901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25551 (p : Pattern) (guard : d128 p = 1) : d2 p ≤ (-1 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare25552 (p : Pattern) (guard : d13 p = 1) : d2 p ≤ (-1 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare25553 (p : Pattern) (guard : d14 p = 1) : d47629 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25552 p hg
    simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25554 (p : Pattern) (guard : d129 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25551 p hg
    simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25553 p hg
    simpa only [d129, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25555 (p : Pattern) (guard : d130 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25554 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25467 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25556 (p : Pattern) (guard : d131 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25555 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25469 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25557 (p : Pattern) (guard : d132 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25556 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25470 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25558 (p : Pattern) (guard : d133 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25557 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25559 (p : Pattern) (guard : d134 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25558 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25560 (p : Pattern) (guard : d135 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25559 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25473 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25561 (p : Pattern) (guard : d136 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25560 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25474 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25562 (p : Pattern) (guard : d137 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25561 p hg
    simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25563 (p : Pattern) (guard : d138 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25562 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25477 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25564 (p : Pattern) (guard : d139 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25563 p hg
    simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25565 (p : Pattern) (guard : d140 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25564 p hg
    simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25566 (p : Pattern) (guard : d141 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25565 p hg
    simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25567 (p : Pattern) (guard : d142 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25566 p hg
    simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25568 (p : Pattern) (guard : d143 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25567 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25486 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25569 (p : Pattern) (guard : d144 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25568 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25488 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25570 (p : Pattern) (guard : d145 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25569 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25489 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25571 (p : Pattern) (guard : d146 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25570 p hg
    simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25572 (p : Pattern) (guard : d147 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25571 p hg
    simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25573 (p : Pattern) (guard : d148 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25572 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25492 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25574 (p : Pattern) (guard : d149 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25573 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25494 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25575 (p : Pattern) (guard : d128 p = 1) : d0 p ≤ (-1 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare25576 (p : Pattern) (guard : d13 p = 1) : d0 p ≤ (-1 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare25577 (p : Pattern) (guard : d14 p = 1) : d47612 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25576 p hg
    simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25578 (p : Pattern) (guard : d129 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25575 p hg
    simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25577 p hg
    simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25579 (p : Pattern) (guard : d130 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25578 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25499 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25580 (p : Pattern) (guard : d131 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25579 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25501 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25581 (p : Pattern) (guard : d132 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25580 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25502 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25582 (p : Pattern) (guard : d133 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25581 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25583 (p : Pattern) (guard : d134 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25582 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25584 (p : Pattern) (guard : d135 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25583 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25505 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25585 (p : Pattern) (guard : d136 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25584 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25506 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25586 (p : Pattern) (guard : d137 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25585 p hg
    simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25587 (p : Pattern) (guard : d138 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25586 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25588 (p : Pattern) (guard : d139 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25587 p hg
    simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25589 (p : Pattern) (guard : d140 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25588 p hg
    simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25590 (p : Pattern) (guard : d141 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25589 p hg
    simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25591 (p : Pattern) (guard : d142 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25590 p hg
    simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25592 (p : Pattern) (guard : d143 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25591 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25518 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25593 (p : Pattern) (guard : d144 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25592 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25519 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25594 (p : Pattern) (guard : d145 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25593 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25520 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25595 (p : Pattern) (guard : d18581 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d145 p = 1 := by simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25594 p hg
    simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25596 (p : Pattern) (guard : d18582 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18581 p = 1 := by simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25595 p hg
    simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25597 (p : Pattern) (guard : d18583 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18582 p = 1 := by simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25596 p hg
    simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18545 p = 1 := by simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25523 p hg
    simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25598 (p : Pattern) (guard : d18584 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18583 p = 1 := by simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25597 p hg
    simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18546 p = 1 := by simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25524 p hg
    simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25599 (p : Pattern) (guard : d187902 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25574 p hg
    simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18584 p = 1 := by simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25598 p hg
    simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25600 (p : Pattern) (guard : d187903 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187902 p = 1 := by simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25599 p hg
    simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25601 (p : Pattern) (guard : d187904 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187903 p = 1 := by simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25600 p hg
    simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25602 (p : Pattern) (guard : d187905 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187904 p = 1 := by simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25601 p hg
    simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187881 p = 1 := by simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25529 p hg
    simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25603 (p : Pattern) (guard : d187906 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187905 p = 1 := by simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25602 p hg
    simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25604 (p : Pattern) (guard : d187907 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187906 p = 1 := by simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25603 p hg
    simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25605 (p : Pattern) (guard : d187908 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187907 p = 1 := by simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25604 p hg
    simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25606 (p : Pattern) (guard : d187909 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187908 p = 1 := by simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25605 p hg
    simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187885 p = 1 := by simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25533 p hg
    simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25607 (p : Pattern) (guard : d187910 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d187909 p = 1 := by simpa only [d187910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25606 p hg
    simpa only [d187910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25608 (p : Pattern) (guard : d187911 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d187910 p = 1 := by simpa only [d187911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25607 p hg
    simpa only [d187911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187887 p = 1 := by simpa only [d187911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25535 p hg
    simpa only [d187911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25609 (p : Pattern) (guard : d187912 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187911 p = 1 := by simpa only [d187912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25608 p hg
    simpa only [d187912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25610 (p : Pattern) (guard : d187913 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187912 p = 1 := by simpa only [d187913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25609 p hg
    simpa only [d187913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25611 (p : Pattern) (guard : d187914 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187914, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d187914, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187913 p = 1 := by simpa only [d187914, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25610 p hg
    simpa only [d187914, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25612 (p : Pattern) (guard : d187915 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187914 p = 1 := by simpa only [d187915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25611 p hg
    simpa only [d187915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25613 (p : Pattern) (guard : d187916 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d187915 p = 1 := by simpa only [d187916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25612 p hg
    simpa only [d187916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25614 (p : Pattern) (guard : d187917 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d187916 p = 1 := by simpa only [d187917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25613 p hg
    simpa only [d187917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25615 (p : Pattern) (guard : d187918 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d187917 p = 1 := by simpa only [d187918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25614 p hg
    simpa only [d187918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25616 (p : Pattern) (guard : d187919 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d187918 p = 1 := by simpa only [d187919, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d187919, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187919, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d187919, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25617 (p : Pattern) (guard : d187920 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187920, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d187920, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187919 p = 1 := by simpa only [d187920, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25616 p hg
    simpa only [d187920, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25618 (p : Pattern) (guard : d187921 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187920 p = 1 := by simpa only [d187921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25617 p hg
    simpa only [d187921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25619 (p : Pattern) (guard : d187922 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187921 p = 1 := by simpa only [d187922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25618 p hg
    simpa only [d187922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25620 (p : Pattern) (guard : d187923 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187922 p = 1 := by simpa only [d187923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25619 p hg
    simpa only [d187923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25621 (p : Pattern) (guard : d187924 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187923 p = 1 := by simpa only [d187924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25620 p hg
    simpa only [d187924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25622 (p : Pattern) (guard : d187925 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d187901 p = 1 := by simpa only [d187925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25550 p hg
    simpa only [d187925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187924 p = 1 := by simpa only [d187925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25621 p hg
    simpa only [d187925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25623 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (-1 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare25624 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (-1 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare25625 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25624 p hg
    simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25626 (p : Pattern) (guard : d309 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25623 p hg
    simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25625 p hg
    simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25627 (p : Pattern) (guard : d310 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25626 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25554 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25628 (p : Pattern) (guard : d311 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25627 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25555 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25629 (p : Pattern) (guard : d312 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25628 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25556 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25630 (p : Pattern) (guard : d313 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25629 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25631 (p : Pattern) (guard : d314 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25630 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25632 (p : Pattern) (guard : d315 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25631 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25559 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25633 (p : Pattern) (guard : d316 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25632 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25560 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25634 (p : Pattern) (guard : d317 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25633 p hg
    simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25635 (p : Pattern) (guard : d318 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25634 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25562 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25636 (p : Pattern) (guard : d319 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25635 p hg
    simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25637 (p : Pattern) (guard : d320 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25636 p hg
    simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25638 (p : Pattern) (guard : d321 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25637 p hg
    simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25639 (p : Pattern) (guard : d322 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25638 p hg
    simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25640 (p : Pattern) (guard : d323 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25639 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25567 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25641 (p : Pattern) (guard : d5448 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25560 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25642 (p : Pattern) (guard : d5449 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5448 p = 1 := by simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25641 p hg
    simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25643 (p : Pattern) (guard : d9381 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5449 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25642 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25477 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25644 (p : Pattern) (guard : d9382 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25643 p hg
    simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25645 (p : Pattern) (guard : d9384 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25644 p hg
    simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25646 (p : Pattern) (guard : d12493 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25645 p hg
    simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25647 (p : Pattern) (guard : d12494 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25646 p hg
    simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25648 (p : Pattern) (guard : d12495 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25647 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25486 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25649 (p : Pattern) (guard : d15966 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25640 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25648 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25650 (p : Pattern) (guard : d15967 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25649 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25569 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25651 (p : Pattern) (guard : d15968 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25650 p hg
    simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25652 (p : Pattern) (guard : d15969 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25651 p hg
    simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25653 (p : Pattern) (guard : d15970 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25652 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25572 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25654 (p : Pattern) (guard : d15971 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25653 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25573 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25655 (p : Pattern) (guard : d307 p = 1) : d0 p ≤ (-1 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare25656 (p : Pattern) (guard : d127 p = 1) : d0 p ≤ (-1 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare25657 (p : Pattern) (guard : d308 p = 1) : d47612 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25656 p hg
    simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25658 (p : Pattern) (guard : d309 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25655 p hg
    simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25657 p hg
    simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25659 (p : Pattern) (guard : d310 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25658 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25578 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25660 (p : Pattern) (guard : d311 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25659 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25579 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25661 (p : Pattern) (guard : d312 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25660 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25580 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25662 (p : Pattern) (guard : d313 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25661 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25663 (p : Pattern) (guard : d314 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25662 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25664 (p : Pattern) (guard : d315 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25663 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25583 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25665 (p : Pattern) (guard : d316 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25664 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25584 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25666 (p : Pattern) (guard : d317 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25665 p hg
    simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25667 (p : Pattern) (guard : d318 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25666 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25586 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25668 (p : Pattern) (guard : d319 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25667 p hg
    simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25669 (p : Pattern) (guard : d320 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25668 p hg
    simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25670 (p : Pattern) (guard : d321 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25669 p hg
    simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25671 (p : Pattern) (guard : d322 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25670 p hg
    simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25672 (p : Pattern) (guard : d323 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25671 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25591 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25673 (p : Pattern) (guard : d5448 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25584 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25674 (p : Pattern) (guard : d5449 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5448 p = 1 := by simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25673 p hg
    simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25675 (p : Pattern) (guard : d9381 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5449 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25674 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25676 (p : Pattern) (guard : d9382 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25675 p hg
    simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25677 (p : Pattern) (guard : d9384 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25676 p hg
    simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25678 (p : Pattern) (guard : d12493 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25677 p hg
    simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25679 (p : Pattern) (guard : d12494 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25678 p hg
    simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25680 (p : Pattern) (guard : d12495 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25679 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25518 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25681 (p : Pattern) (guard : d15966 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25672 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25680 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25682 (p : Pattern) (guard : d15967 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25681 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25593 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25683 (p : Pattern) (guard : d18645 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d15967 p = 1 := by simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25682 p hg
    simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25684 (p : Pattern) (guard : d18646 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18645 p = 1 := by simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25683 p hg
    simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25685 (p : Pattern) (guard : d18647 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18646 p = 1 := by simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25684 p hg
    simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18582 p = 1 := by simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25596 p hg
    simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25686 (p : Pattern) (guard : d18648 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18647 p = 1 := by simpa only [d18648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25685 p hg
    simpa only [d18648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18583 p = 1 := by simpa only [d18648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25597 p hg
    simpa only [d18648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25687 (p : Pattern) (guard : d187926 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d15971 p = 1 := by simpa only [d187926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25654 p hg
    simpa only [d187926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18648 p = 1 := by simpa only [d187926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25686 p hg
    simpa only [d187926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25688 (p : Pattern) (guard : d187927 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187926 p = 1 := by simpa only [d187927, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25687 p hg
    simpa only [d187927, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187927, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d187927, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25689 (p : Pattern) (guard : d187928 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187928, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d187928, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187927 p = 1 := by simpa only [d187928, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25688 p hg
    simpa only [d187928, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25690 (p : Pattern) (guard : d187929 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187928 p = 1 := by simpa only [d187929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25689 p hg
    simpa only [d187929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187904 p = 1 := by simpa only [d187929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25601 p hg
    simpa only [d187929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25691 (p : Pattern) (guard : d187930 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187929 p = 1 := by simpa only [d187930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25690 p hg
    simpa only [d187930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25692 (p : Pattern) (guard : d187931 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187930 p = 1 := by simpa only [d187931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25691 p hg
    simpa only [d187931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25693 (p : Pattern) (guard : d187932 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187931 p = 1 := by simpa only [d187932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25692 p hg
    simpa only [d187932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25694 (p : Pattern) (guard : d187933 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187932 p = 1 := by simpa only [d187933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25693 p hg
    simpa only [d187933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187908 p = 1 := by simpa only [d187933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25605 p hg
    simpa only [d187933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25695 (p : Pattern) (guard : d187934 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d187933 p = 1 := by simpa only [d187934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25694 p hg
    simpa only [d187934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25696 (p : Pattern) (guard : d187935 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187904 p = 1 := by simpa only [d187935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25601 p hg
    simpa only [d187935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25697 (p : Pattern) (guard : d187936 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187935 p = 1 := by simpa only [d187936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25696 p hg
    simpa only [d187936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25698 (p : Pattern) (guard : d187937 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187936 p = 1 := by simpa only [d187937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25697 p hg
    simpa only [d187937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25699 (p : Pattern) (guard : d187938 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187937 p = 1 := by simpa only [d187938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25698 p hg
    simpa only [d187938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25700 (p : Pattern) (guard : d187939 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187938 p = 1 := by simpa only [d187939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25699 p hg
    simpa only [d187939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25701 (p : Pattern) (guard : d187940 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d187939 p = 1 := by simpa only [d187940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25700 p hg
    simpa only [d187940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25702 (p : Pattern) (guard : d187941 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d187934 p = 1 := by simpa only [d187941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25695 p hg
    simpa only [d187941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187940 p = 1 := by simpa only [d187941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25701 p hg
    simpa only [d187941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25703 (p : Pattern) (guard : d187942 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187941 p = 1 := by simpa only [d187942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25702 p hg
    simpa only [d187942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25704 (p : Pattern) (guard : d187943 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187942 p = 1 := by simpa only [d187943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25703 p hg
    simpa only [d187943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25705 (p : Pattern) (guard : d187944 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187944, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d187944, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187943 p = 1 := by simpa only [d187944, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25704 p hg
    simpa only [d187944, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25706 (p : Pattern) (guard : d187945 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187944 p = 1 := by simpa only [d187945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25705 p hg
    simpa only [d187945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25707 (p : Pattern) (guard : d187946 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187886 p = 1 := by simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25534 p hg
    simpa only [d187946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25708 (p : Pattern) (guard : d187947 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d187946 p = 1 := by simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25707 p hg
    simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25709 (p : Pattern) (guard : d187948 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187947 p = 1 := by simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25708 p hg
    simpa only [d187948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25710 (p : Pattern) (guard : d187949 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187948 p = 1 := by simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25709 p hg
    simpa only [d187949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25711 (p : Pattern) (guard : d187950 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187949 p = 1 := by simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25710 p hg
    simpa only [d187950, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25712 (p : Pattern) (guard : d187951 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187950 p = 1 := by simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25711 p hg
    simpa only [d187951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25713 (p : Pattern) (guard : d187952 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d187945 p = 1 := by simpa only [d187952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25706 p hg
    simpa only [d187952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187951 p = 1 := by simpa only [d187952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25712 p hg
    simpa only [d187952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25714 (p : Pattern) (guard : d187953 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d187952 p = 1 := by simpa only [d187953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25713 p hg
    simpa only [d187953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25715 (p : Pattern) (guard : d187954 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d187953 p = 1 := by simpa only [d187954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25714 p hg
    simpa only [d187954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25716 (p : Pattern) (guard : d187955 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d187954 p = 1 := by simpa only [d187955, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25715 p hg
    simpa only [d187955, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187955, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d187955, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25717 (p : Pattern) (guard : d187956 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187956, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d187956, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187955 p = 1 := by simpa only [d187956, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25716 p hg
    simpa only [d187956, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25718 (p : Pattern) (guard : d187957 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187956 p = 1 := by simpa only [d187957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25717 p hg
    simpa only [d187957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25719 (p : Pattern) (guard : d187958 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187957 p = 1 := by simpa only [d187958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25718 p hg
    simpa only [d187958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25720 (p : Pattern) (guard : d187959 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187958 p = 1 := by simpa only [d187959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25719 p hg
    simpa only [d187959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25721 (p : Pattern) (guard : d187960 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187959 p = 1 := by simpa only [d187960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25720 p hg
    simpa only [d187960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25722 (p : Pattern) (guard : d187961 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d187961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187960 p = 1 := by simpa only [d187961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25721 p hg
    simpa only [d187961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25723 (p : Pattern) (guard : d187962 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d187925 p = 1 := by simpa only [d187962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25622 p hg
    simpa only [d187962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187961 p = 1 := by simpa only [d187962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25722 p hg
    simpa only [d187962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25724 (p : Pattern) (guard : d528 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25626 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25725 (p : Pattern) (guard : d529 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25724 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25627 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25726 (p : Pattern) (guard : d530 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25725 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25628 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25727 (p : Pattern) (guard : d531 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25726 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25728 (p : Pattern) (guard : d532 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25727 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25729 (p : Pattern) (guard : d533 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25728 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25631 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25730 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25554 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25731 (p : Pattern) (guard : d535 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25627 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25730 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25732 (p : Pattern) (guard : d536 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25731 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25556 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25733 (p : Pattern) (guard : d537 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25732 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25734 (p : Pattern) (guard : d538 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25733 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25735 (p : Pattern) (guard : d539 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25734 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25559 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25736 (p : Pattern) (guard : d540 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25729 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25735 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25737 (p : Pattern) (guard : d541 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25736 p hg
    simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25738 (p : Pattern) (guard : d542 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25737 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25634 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25739 (p : Pattern) (guard : d543 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25738 p hg
    simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25740 (p : Pattern) (guard : d544 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25739 p hg
    simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25741 (p : Pattern) (guard : d545 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25740 p hg
    simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25742 (p : Pattern) (guard : d546 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25741 p hg
    simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25743 (p : Pattern) (guard : d5010 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25730 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25469 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25744 (p : Pattern) (guard : d5011 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25743 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25470 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25745 (p : Pattern) (guard : d9452 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25744 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25746 (p : Pattern) (guard : d9453 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25745 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25747 (p : Pattern) (guard : d9454 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9453 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25746 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25473 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25748 (p : Pattern) (guard : d9455 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9454 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25747 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25749 (p : Pattern) (guard : d9456 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9455 p = 1 := by simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25748 p hg
    simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
