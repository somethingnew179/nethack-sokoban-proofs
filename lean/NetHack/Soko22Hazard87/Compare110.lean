import NetHack.Soko22Hazard87.Compare109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27500 (p : Pattern) (guard : d131 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27499 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27412 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27501 (p : Pattern) (guard : d132 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27500 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27413 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27502 (p : Pattern) (guard : d133 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27501 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27503 (p : Pattern) (guard : d134 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27502 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27504 (p : Pattern) (guard : d135 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27503 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27416 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27505 (p : Pattern) (guard : d136 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27504 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27417 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27506 (p : Pattern) (guard : d137 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27505 p hg
    simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d137, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27507 (p : Pattern) (guard : d138 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27506 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27420 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27508 (p : Pattern) (guard : d139 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27507 p hg
    simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d139, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27509 (p : Pattern) (guard : d140 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27508 p hg
    simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d140, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27510 (p : Pattern) (guard : d141 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27509 p hg
    simpa only [d141, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27511 (p : Pattern) (guard : d142 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27510 p hg
    simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d142, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27512 (p : Pattern) (guard : d143 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27511 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27429 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27513 (p : Pattern) (guard : d144 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27512 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27431 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27514 (p : Pattern) (guard : d145 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27513 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27432 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27515 (p : Pattern) (guard : d146 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27514 p hg
    simpa only [d146, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27516 (p : Pattern) (guard : d147 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27515 p hg
    simpa only [d147, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27517 (p : Pattern) (guard : d148 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27516 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27435 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27518 (p : Pattern) (guard : d149 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27517 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27437 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27519 (p : Pattern) (guard : d128 p = 1) : d0 p ≤ (-2 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare27520 (p : Pattern) (guard : d13 p = 1) : d0 p ≤ (-2 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare27521 (p : Pattern) (guard : d14 p = 1) : d47612 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27520 p hg
    simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d14, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27522 (p : Pattern) (guard : d129 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27519 p hg
    simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27521 p hg
    simpa only [d129, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27523 (p : Pattern) (guard : d130 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27522 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27442 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27524 (p : Pattern) (guard : d131 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27523 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27444 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27525 (p : Pattern) (guard : d132 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27524 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27445 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27526 (p : Pattern) (guard : d133 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27525 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27527 (p : Pattern) (guard : d134 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27526 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27528 (p : Pattern) (guard : d135 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27527 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27448 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27529 (p : Pattern) (guard : d136 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27528 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27449 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27530 (p : Pattern) (guard : d137 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27529 p hg
    simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d137, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27531 (p : Pattern) (guard : d138 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27530 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27452 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27532 (p : Pattern) (guard : d139 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27531 p hg
    simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d139, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27533 (p : Pattern) (guard : d140 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27532 p hg
    simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d140, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27534 (p : Pattern) (guard : d141 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27533 p hg
    simpa only [d141, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27535 (p : Pattern) (guard : d142 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27534 p hg
    simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d142, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27536 (p : Pattern) (guard : d143 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27535 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27461 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27537 (p : Pattern) (guard : d144 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27536 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27462 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27538 (p : Pattern) (guard : d145 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27537 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27463 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27539 (p : Pattern) (guard : d18581 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d145 p = 1 := by simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27538 p hg
    simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d18581, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27540 (p : Pattern) (guard : d18582 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18581 p = 1 := by simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27539 p hg
    simpa only [d18582, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27541 (p : Pattern) (guard : d18583 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18582 p = 1 := by simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27540 p hg
    simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18545 p = 1 := by simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27466 p hg
    simpa only [d18583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27542 (p : Pattern) (guard : d18584 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18583 p = 1 := by simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27541 p hg
    simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18546 p = 1 := by simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27467 p hg
    simpa only [d18584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27543 (p : Pattern) (guard : d187902 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27518 p hg
    simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18584 p = 1 := by simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27542 p hg
    simpa only [d187902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27544 (p : Pattern) (guard : d187903 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187902 p = 1 := by simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27543 p hg
    simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d187903, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27545 (p : Pattern) (guard : d187904 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187903 p = 1 := by simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27544 p hg
    simpa only [d187904, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27546 (p : Pattern) (guard : d187905 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187904 p = 1 := by simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27545 p hg
    simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187881 p = 1 := by simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27472 p hg
    simpa only [d187905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27547 (p : Pattern) (guard : d187906 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187905 p = 1 := by simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27546 p hg
    simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27548 (p : Pattern) (guard : d187907 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187906 p = 1 := by simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27547 p hg
    simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27549 (p : Pattern) (guard : d187908 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187907 p = 1 := by simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27548 p hg
    simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27550 (p : Pattern) (guard : d187909 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187908 p = 1 := by simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27549 p hg
    simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187885 p = 1 := by simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27476 p hg
    simpa only [d187909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27551 (p : Pattern) (guard : d188300 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187909 p = 1 := by simpa only [d188300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27550 p hg
    simpa only [d188300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27552 (p : Pattern) (guard : d188301 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188300 p = 1 := by simpa only [d188301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27551 p hg
    simpa only [d188301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27553 (p : Pattern) (guard : d188302 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188301 p = 1 := by simpa only [d188302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27552 p hg
    simpa only [d188302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27554 (p : Pattern) (guard : d188303 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188302 p = 1 := by simpa only [d188303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27553 p hg
    simpa only [d188303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27555 (p : Pattern) (guard : d188304 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188304, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d188304, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188303 p = 1 := by simpa only [d188304, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27554 p hg
    simpa only [d188304, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27556 (p : Pattern) (guard : d188305 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188304 p = 1 := by simpa only [d188305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27555 p hg
    simpa only [d188305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27557 (p : Pattern) (guard : d188306 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188305 p = 1 := by simpa only [d188306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27556 p hg
    simpa only [d188306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27558 (p : Pattern) (guard : d188307 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188306 p = 1 := by simpa only [d188307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27557 p hg
    simpa only [d188307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27559 (p : Pattern) (guard : d188308 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188307 p = 1 := by simpa only [d188308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27558 p hg
    simpa only [d188308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27560 (p : Pattern) (guard : d188309 p = 1) : d48748 p ≤ (-2 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188308 p = 1 := by simpa only [d188309, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27559 p hg
    simpa only [d188309, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188309, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d188309, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27561 (p : Pattern) (guard : d188310 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188310, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d188310, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188309 p = 1 := by simpa only [d188310, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27560 p hg
    simpa only [d188310, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27562 (p : Pattern) (guard : d188311 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188310 p = 1 := by simpa only [d188311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27561 p hg
    simpa only [d188311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27563 (p : Pattern) (guard : d188312 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188311 p = 1 := by simpa only [d188312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27562 p hg
    simpa only [d188312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27564 (p : Pattern) (guard : d188313 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188312 p = 1 := by simpa only [d188313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27563 p hg
    simpa only [d188313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27565 (p : Pattern) (guard : d188314 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188313 p = 1 := by simpa only [d188314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27564 p hg
    simpa only [d188314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27566 (p : Pattern) (guard : d188315 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188314 p = 1 := by simpa only [d188315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27565 p hg
    simpa only [d188315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27567 (p : Pattern) (guard : d188316 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d188299 p = 1 := by simpa only [d188316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27494 p hg
    simpa only [d188316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188315 p = 1 := by simpa only [d188316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27566 p hg
    simpa only [d188316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27568 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (-2 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare27569 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (-2 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare27570 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27569 p hg
    simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d308, d47629, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27571 (p : Pattern) (guard : d309 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27568 p hg
    simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27570 p hg
    simpa only [d309, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27572 (p : Pattern) (guard : d310 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27571 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27498 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27573 (p : Pattern) (guard : d311 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27572 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27499 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27574 (p : Pattern) (guard : d312 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27573 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27500 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27575 (p : Pattern) (guard : d313 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27574 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27576 (p : Pattern) (guard : d314 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27575 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27577 (p : Pattern) (guard : d315 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27576 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27503 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27578 (p : Pattern) (guard : d316 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27577 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27504 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27579 (p : Pattern) (guard : d317 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27578 p hg
    simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d317, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27580 (p : Pattern) (guard : d318 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27579 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27506 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27581 (p : Pattern) (guard : d319 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27580 p hg
    simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d319, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27582 (p : Pattern) (guard : d320 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27581 p hg
    simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d320, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27583 (p : Pattern) (guard : d321 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27582 p hg
    simpa only [d321, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27584 (p : Pattern) (guard : d322 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27583 p hg
    simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d322, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27585 (p : Pattern) (guard : d323 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27584 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27511 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27586 (p : Pattern) (guard : d5448 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27504 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27587 (p : Pattern) (guard : d5449 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5448 p = 1 := by simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27586 p hg
    simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d5449, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27588 (p : Pattern) (guard : d9381 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5449 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27587 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27420 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27589 (p : Pattern) (guard : d9382 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27588 p hg
    simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d9382, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27590 (p : Pattern) (guard : d9384 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27589 p hg
    simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d9384, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27591 (p : Pattern) (guard : d12493 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27590 p hg
    simpa only [d12493, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27592 (p : Pattern) (guard : d12494 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27591 p hg
    simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d12494, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27593 (p : Pattern) (guard : d12495 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27592 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27429 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27594 (p : Pattern) (guard : d15966 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27585 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27593 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27595 (p : Pattern) (guard : d15967 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27594 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27513 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27596 (p : Pattern) (guard : d15968 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27595 p hg
    simpa only [d15968, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27597 (p : Pattern) (guard : d15969 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27596 p hg
    simpa only [d15969, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27598 (p : Pattern) (guard : d15970 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27597 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27516 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27599 (p : Pattern) (guard : d475 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27516 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27600 (p : Pattern) (guard : d16035 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27598 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27599 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27601 (p : Pattern) (guard : d307 p = 1) : d0 p ≤ (-2 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare27602 (p : Pattern) (guard : d127 p = 1) : d0 p ≤ (-2 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare27603 (p : Pattern) (guard : d308 p = 1) : d47612 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27602 p hg
    simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d308, d47612, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27604 (p : Pattern) (guard : d309 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27601 p hg
    simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27603 p hg
    simpa only [d309, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27605 (p : Pattern) (guard : d310 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27604 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27522 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27606 (p : Pattern) (guard : d311 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27605 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27523 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27607 (p : Pattern) (guard : d312 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27606 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27524 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27608 (p : Pattern) (guard : d313 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27607 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27609 (p : Pattern) (guard : d314 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27608 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27610 (p : Pattern) (guard : d315 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27609 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27527 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27611 (p : Pattern) (guard : d316 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27610 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27528 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27612 (p : Pattern) (guard : d317 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27611 p hg
    simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d317, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27613 (p : Pattern) (guard : d318 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27612 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27530 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27614 (p : Pattern) (guard : d319 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27613 p hg
    simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d319, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27615 (p : Pattern) (guard : d320 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27614 p hg
    simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d320, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27616 (p : Pattern) (guard : d321 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27615 p hg
    simpa only [d321, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27617 (p : Pattern) (guard : d322 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27616 p hg
    simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d322, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27618 (p : Pattern) (guard : d323 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27617 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27535 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27619 (p : Pattern) (guard : d5448 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27528 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27620 (p : Pattern) (guard : d5449 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5448 p = 1 := by simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27619 p hg
    simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d5449, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27621 (p : Pattern) (guard : d9381 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5449 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27620 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27452 p hg
    simpa only [d9381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27622 (p : Pattern) (guard : d9382 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27621 p hg
    simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d9382, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27623 (p : Pattern) (guard : d9384 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27622 p hg
    simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d9384, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27624 (p : Pattern) (guard : d12493 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27623 p hg
    simpa only [d12493, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27625 (p : Pattern) (guard : d12494 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27624 p hg
    simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d12494, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27626 (p : Pattern) (guard : d12495 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27625 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27461 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27627 (p : Pattern) (guard : d15966 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27618 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27626 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27628 (p : Pattern) (guard : d15967 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27627 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27537 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27629 (p : Pattern) (guard : d18645 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d15967 p = 1 := by simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27628 p hg
    simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d18645, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27630 (p : Pattern) (guard : d18646 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18645 p = 1 := by simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27629 p hg
    simpa only [d18646, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27631 (p : Pattern) (guard : d18647 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18646 p = 1 := by simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27630 p hg
    simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18582 p = 1 := by simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27540 p hg
    simpa only [d18647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27632 (p : Pattern) (guard : d18740 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18582 p = 1 := by simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27540 p hg
    simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27633 (p : Pattern) (guard : d18741 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18647 p = 1 := by simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27631 p hg
    simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18740 p = 1 := by simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27632 p hg
    simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27634 (p : Pattern) (guard : d187966 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27600 p hg
    simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18741 p = 1 := by simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27633 p hg
    simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27635 (p : Pattern) (guard : d187967 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187966 p = 1 := by simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27634 p hg
    simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27636 (p : Pattern) (guard : d187968 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187967 p = 1 := by simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27635 p hg
    simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27637 (p : Pattern) (guard : d480 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27599 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27638 (p : Pattern) (guard : d18750 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18740 p = 1 := by simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27632 p hg
    simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27639 (p : Pattern) (guard : d187973 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27637 p hg
    simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18750 p = 1 := by simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27638 p hg
    simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27640 (p : Pattern) (guard : d187974 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187973 p = 1 := by simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27639 p hg
    simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27641 (p : Pattern) (guard : d187975 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187974 p = 1 := by simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27640 p hg
    simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27642 (p : Pattern) (guard : d187976 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187968 p = 1 := by simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27636 p hg
    simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187975 p = 1 := by simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27641 p hg
    simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27643 (p : Pattern) (guard : d187977 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187976 p = 1 := by simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27642 p hg
    simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27644 (p : Pattern) (guard : d187978 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187977 p = 1 := by simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27643 p hg
    simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27645 (p : Pattern) (guard : d187979 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187978 p = 1 := by simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27644 p hg
    simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27646 (p : Pattern) (guard : d187993 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187975 p = 1 := by simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27641 p hg
    simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27647 (p : Pattern) (guard : d187994 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187993 p = 1 := by simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27646 p hg
    simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27648 (p : Pattern) (guard : d187995 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187994 p = 1 := by simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27647 p hg
    simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27649 (p : Pattern) (guard : d187996 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187995 p = 1 := by simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27648 p hg
    simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27650 (p : Pattern) (guard : d188317 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187979 p = 1 := by simpa only [d188317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27645 p hg
    simpa only [d188317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187996 p = 1 := by simpa only [d188317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27649 p hg
    simpa only [d188317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27651 (p : Pattern) (guard : d188318 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188317 p = 1 := by simpa only [d188318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27650 p hg
    simpa only [d188318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27652 (p : Pattern) (guard : d188319 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188318 p = 1 := by simpa only [d188319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27651 p hg
    simpa only [d188319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27653 (p : Pattern) (guard : d188320 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188319 p = 1 := by simpa only [d188320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27652 p hg
    simpa only [d188320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27654 (p : Pattern) (guard : d188321 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188320 p = 1 := by simpa only [d188321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27653 p hg
    simpa only [d188321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27655 (p : Pattern) (guard : d188322 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188322, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d188322, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188321 p = 1 := by simpa only [d188322, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27654 p hg
    simpa only [d188322, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27656 (p : Pattern) (guard : d188323 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188322 p = 1 := by simpa only [d188323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27655 p hg
    simpa only [d188323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27657 (p : Pattern) (guard : d188324 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188323 p = 1 := by simpa only [d188324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27656 p hg
    simpa only [d188324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27658 (p : Pattern) (guard : d188325 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188324 p = 1 := by simpa only [d188325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27657 p hg
    simpa only [d188325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27659 (p : Pattern) (guard : d188326 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188325 p = 1 := by simpa only [d188326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27658 p hg
    simpa only [d188326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27660 (p : Pattern) (guard : d188327 p = 1) : d48748 p ≤ (-2 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188326 p = 1 := by simpa only [d188327, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27659 p hg
    simpa only [d188327, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188327, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d188327, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27661 (p : Pattern) (guard : d188328 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188328, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d188328, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188327 p = 1 := by simpa only [d188328, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27660 p hg
    simpa only [d188328, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27662 (p : Pattern) (guard : d188329 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188328 p = 1 := by simpa only [d188329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27661 p hg
    simpa only [d188329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27663 (p : Pattern) (guard : d188330 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188329 p = 1 := by simpa only [d188330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27662 p hg
    simpa only [d188330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27664 (p : Pattern) (guard : d188331 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188330 p = 1 := by simpa only [d188331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27663 p hg
    simpa only [d188331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27665 (p : Pattern) (guard : d188332 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188331 p = 1 := by simpa only [d188332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27664 p hg
    simpa only [d188332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27666 (p : Pattern) (guard : d188333 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188332 p = 1 := by simpa only [d188333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27665 p hg
    simpa only [d188333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27667 (p : Pattern) (guard : d188334 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188333 p = 1 := by simpa only [d188334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27666 p hg
    simpa only [d188334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27668 (p : Pattern) (guard : d188335 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d188316 p = 1 := by simpa only [d188335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27567 p hg
    simpa only [d188335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188334 p = 1 := by simpa only [d188335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27667 p hg
    simpa only [d188335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27669 (p : Pattern) (guard : d528 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27571 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27670 (p : Pattern) (guard : d529 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27669 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27572 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27671 (p : Pattern) (guard : d530 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27670 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27573 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27672 (p : Pattern) (guard : d531 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27671 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27673 (p : Pattern) (guard : d532 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27672 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27674 (p : Pattern) (guard : d533 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27673 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27576 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27675 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27498 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27676 (p : Pattern) (guard : d535 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27572 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27675 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27677 (p : Pattern) (guard : d536 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27676 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27500 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27678 (p : Pattern) (guard : d537 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27677 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27679 (p : Pattern) (guard : d538 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27678 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27680 (p : Pattern) (guard : d539 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27679 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27503 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27681 (p : Pattern) (guard : d540 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27674 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27680 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27682 (p : Pattern) (guard : d541 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27681 p hg
    simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d541, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27683 (p : Pattern) (guard : d542 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27682 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27579 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27684 (p : Pattern) (guard : d543 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27683 p hg
    simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d543, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27685 (p : Pattern) (guard : d544 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27684 p hg
    simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d544, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27686 (p : Pattern) (guard : d545 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27685 p hg
    simpa only [d545, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27687 (p : Pattern) (guard : d546 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27686 p hg
    simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d546, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27688 (p : Pattern) (guard : d5010 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27675 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27412 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27689 (p : Pattern) (guard : d5011 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27688 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27413 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27690 (p : Pattern) (guard : d9452 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27689 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27691 (p : Pattern) (guard : d9453 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27690 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27692 (p : Pattern) (guard : d9454 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9453 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27691 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27416 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27693 (p : Pattern) (guard : d9455 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9454 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27692 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27694 (p : Pattern) (guard : d9456 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9455 p = 1 := by simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27693 p hg
    simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d9456, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27695 (p : Pattern) (guard : d9457 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27579 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27694 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27696 (p : Pattern) (guard : d9458 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27695 p hg
    simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27697 (p : Pattern) (guard : d9460 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27696 p hg
    simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27698 (p : Pattern) (guard : d16073 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27697 p hg
    simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27699 (p : Pattern) (guard : d16074 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27698 p hg
    simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27700 (p : Pattern) (guard : d16075 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27687 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27699 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27701 (p : Pattern) (guard : d9464 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27576 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27691 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27702 (p : Pattern) (guard : d9465 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9464 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27701 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27703 (p : Pattern) (guard : d9466 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9465 p = 1 := by simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27702 p hg
    simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27704 (p : Pattern) (guard : d9467 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9466 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27703 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27694 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27705 (p : Pattern) (guard : d9468 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27704 p hg
    simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27706 (p : Pattern) (guard : d9470 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27705 p hg
    simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27707 (p : Pattern) (guard : d12748 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27706 p hg
    simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27708 (p : Pattern) (guard : d12749 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27707 p hg
    simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27709 (p : Pattern) (guard : d750 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27506 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27710 (p : Pattern) (guard : d751 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27709 p hg
    simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27711 (p : Pattern) (guard : d752 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27710 p hg
    simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27712 (p : Pattern) (guard : d753 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27711 p hg
    simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27713 (p : Pattern) (guard : d754 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27712 p hg
    simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27714 (p : Pattern) (guard : d12750 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27708 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27713 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27715 (p : Pattern) (guard : d16227 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27700 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27714 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27716 (p : Pattern) (guard : d755 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27584 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27713 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27717 (p : Pattern) (guard : d757 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27713 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27718 (p : Pattern) (guard : d758 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27716 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27717 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27719 (p : Pattern) (guard : d16228 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27715 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27718 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27720 (p : Pattern) (guard : d16229 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27719 p hg
    simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27721 (p : Pattern) (guard : d16230 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27720 p hg
    simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27722 (p : Pattern) (guard : d762 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27717 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27723 (p : Pattern) (guard : d763 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27718 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27722 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27724 (p : Pattern) (guard : d764 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27723 p hg
    simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27725 (p : Pattern) (guard : d765 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27724 p hg
    simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27726 (p : Pattern) (guard : d16231 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27721 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27725 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27727 (p : Pattern) (guard : d767 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27725 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27728 (p : Pattern) (guard : d16232 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27726 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27727 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27729 (p : Pattern) (guard : d528 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27604 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27730 (p : Pattern) (guard : d529 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27729 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27605 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27731 (p : Pattern) (guard : d530 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27730 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27606 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27732 (p : Pattern) (guard : d531 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27731 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27733 (p : Pattern) (guard : d532 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27732 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27734 (p : Pattern) (guard : d533 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27733 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27609 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27735 (p : Pattern) (guard : d534 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27522 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27736 (p : Pattern) (guard : d535 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27605 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27735 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27737 (p : Pattern) (guard : d536 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27736 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27524 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27738 (p : Pattern) (guard : d537 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27737 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27739 (p : Pattern) (guard : d538 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27738 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27740 (p : Pattern) (guard : d539 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27739 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27527 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27741 (p : Pattern) (guard : d540 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27734 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27740 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27742 (p : Pattern) (guard : d541 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27741 p hg
    simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27743 (p : Pattern) (guard : d542 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27742 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27612 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27744 (p : Pattern) (guard : d543 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27743 p hg
    simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27745 (p : Pattern) (guard : d544 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27744 p hg
    simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27746 (p : Pattern) (guard : d545 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27745 p hg
    simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27747 (p : Pattern) (guard : d546 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27746 p hg
    simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27748 (p : Pattern) (guard : d5010 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27735 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27444 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27749 (p : Pattern) (guard : d5011 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27748 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27445 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
