/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons188
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26460 (p : Pattern) (guard : d6326 p = 1) : d125 p ≤ (0 : Int) + d6417 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d125, d6417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26438 p hg
    simpa only [d125, d6417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d125, d6417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d125, d6417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26461 (p : Pattern) (guard : d6326 p = 1) : d126 p ≤ (0 : Int) + d6418 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d126, d6418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26459 p hg
    simpa only [d126, d6418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d126, d6418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26460 p hg
    simpa only [d126, d6418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26462 (p : Pattern) (guard : d6326 p = 1) : d127 p ≤ (0 : Int) + d6419 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d127, d6419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26458 p hg
    simpa only [d127, d6419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d127, d6419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26461 p hg
    simpa only [d127, d6419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26463 (p : Pattern) (guard : d6326 p = 1) : d128 p ≤ (0 : Int) + d6420 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d128, d6420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26397 p hg
    simpa only [d128, d6420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d128, d6420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d128, d6420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26464 (p : Pattern) (guard : d6326 p = 1) : d129 p ≤ (0 : Int) + d6421 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d129, d6421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26461 p hg
    simpa only [d129, d6421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d129, d6421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26463 p hg
    simpa only [d129, d6421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26465 (p : Pattern) (guard : d6326 p = 1) : d130 p ≤ (0 : Int) + d6422 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d130, d6422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26462 p hg
    simpa only [d130, d6422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d130, d6422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26464 p hg
    simpa only [d130, d6422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26466 (p : Pattern) (guard : d6326 p = 1) : d131 p ≤ (0 : Int) + d6423 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d131, d6423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26445 p hg
    simpa only [d131, d6423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d131, d6423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26465 p hg
    simpa only [d131, d6423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26467 (p : Pattern) (guard : d6326 p = 1) : d132 p ≤ (0 : Int) + d6424 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d132, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26449 p hg
    simpa only [d132, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d132, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26450 p hg
    simpa only [d132, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26468 (p : Pattern) (guard : d6326 p = 1) : d133 p ≤ (0 : Int) + d6425 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d133, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26434 p hg
    simpa only [d133, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d133, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26467 p hg
    simpa only [d133, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26469 (p : Pattern) (guard : d6326 p = 1) : d134 p ≤ (0 : Int) + d6426 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d134, d6426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26440 p hg
    simpa only [d134, d6426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d134, d6426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26387 p hg
    simpa only [d134, d6426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26470 (p : Pattern) (guard : d6326 p = 1) : d135 p ≤ (0 : Int) + d6427 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d135, d6427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26468 p hg
    simpa only [d135, d6427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d135, d6427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26469 p hg
    simpa only [d135, d6427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26471 (p : Pattern) (guard : d6326 p = 1) : d136 p ≤ (0 : Int) + d6428 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d136, d6428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26440 p hg
    simpa only [d136, d6428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d136, d6428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26389 p hg
    simpa only [d136, d6428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26472 (p : Pattern) (guard : d6326 p = 1) : d137 p ≤ (0 : Int) + d6429 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d137, d6429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26471 p hg
    simpa only [d137, d6429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d137, d6429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d137, d6429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26473 (p : Pattern) (guard : d6326 p = 1) : d138 p ≤ (0 : Int) + d6430 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d138, d6430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26470 p hg
    simpa only [d138, d6430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d138, d6430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26472 p hg
    simpa only [d138, d6430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26474 (p : Pattern) (guard : d6326 p = 1) : d139 p ≤ (0 : Int) + d6431 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d139, d6431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26449 p hg
    simpa only [d139, d6431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d139, d6431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d139, d6431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26475 (p : Pattern) (guard : d6326 p = 1) : d140 p ≤ (0 : Int) + d6432 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d140, d6432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26457 p hg
    simpa only [d140, d6432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d140, d6432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26474 p hg
    simpa only [d140, d6432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26476 (p : Pattern) (guard : d6326 p = 1) : d141 p ≤ (0 : Int) + d6433 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d141, d6433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26460 p hg
    simpa only [d141, d6433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d141, d6433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26397 p hg
    simpa only [d141, d6433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26477 (p : Pattern) (guard : d6326 p = 1) : d142 p ≤ (0 : Int) + d6434 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d142, d6434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26475 p hg
    simpa only [d142, d6434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d142, d6434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26476 p hg
    simpa only [d142, d6434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26478 (p : Pattern) (guard : d6326 p = 1) : d143 p ≤ (0 : Int) + d6435 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d143, d6435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26460 p hg
    simpa only [d143, d6435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d143, d6435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26399 p hg
    simpa only [d143, d6435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26479 (p : Pattern) (guard : d6326 p = 1) : d144 p ≤ (0 : Int) + d6436 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d144, d6436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26478 p hg
    simpa only [d144, d6436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d144, d6436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d144, d6436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26480 (p : Pattern) (guard : d6326 p = 1) : d145 p ≤ (0 : Int) + d6437 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d145, d6437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26477 p hg
    simpa only [d145, d6437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d145, d6437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26479 p hg
    simpa only [d145, d6437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26481 (p : Pattern) (guard : d6326 p = 1) : d146 p ≤ (0 : Int) + d6438 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d146, d6438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26473 p hg
    simpa only [d146, d6438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d146, d6438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26480 p hg
    simpa only [d146, d6438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26482 (p : Pattern) (guard : d6326 p = 1) : d147 p ≤ (0 : Int) + d6439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d147, d6439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26466 p hg
    simpa only [d147, d6439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d147, d6439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26481 p hg
    simpa only [d147, d6439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26483 (p : Pattern) (guard : d6326 p = 1) : d148 p ≤ (0 : Int) + d6440 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d148, d6440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26455 p hg
    simpa only [d148, d6440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d148, d6440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26456 p hg
    simpa only [d148, d6440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26484 (p : Pattern) (guard : d6326 p = 1) : d149 p ≤ (0 : Int) + d6441 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d149, d6441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26467 p hg
    simpa only [d149, d6441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d149, d6441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26483 p hg
    simpa only [d149, d6441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26485 (p : Pattern) (guard : d6326 p = 1) : d150 p ≤ (0 : Int) + d6442 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d150, d6442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26484 p hg
    simpa only [d150, d6442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d150, d6442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d150, d6442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26486 (p : Pattern) (guard : d6326 p = 1) : d151 p ≤ (0 : Int) + d6443 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d151, d6443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26485 p hg
    simpa only [d151, d6443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d151, d6443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d151, d6443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26487 (p : Pattern) (guard : d6326 p = 1) : d152 p ≤ (0 : Int) + d6444 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d152, d6444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26445 p hg
    simpa only [d152, d6444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d152, d6444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26486 p hg
    simpa only [d152, d6444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26488 (p : Pattern) (guard : d6326 p = 1) : d153 p ≤ (0 : Int) + d6445 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d153, d6445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26483 p hg
    simpa only [d153, d6445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d153, d6445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d153, d6445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26489 (p : Pattern) (guard : d6326 p = 1) : d154 p ≤ (0 : Int) + d6446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d154, d6446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26488 p hg
    simpa only [d154, d6446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d154, d6446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d154, d6446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26490 (p : Pattern) (guard : d6326 p = 1) : d155 p ≤ (0 : Int) + d6447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d155, d6447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26489 p hg
    simpa only [d155, d6447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d155, d6447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d155, d6447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26491 (p : Pattern) (guard : d6326 p = 1) : d156 p ≤ (0 : Int) + d6448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d156, d6448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26473 p hg
    simpa only [d156, d6448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d156, d6448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26490 p hg
    simpa only [d156, d6448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26492 (p : Pattern) (guard : d6326 p = 1) : d157 p ≤ (0 : Int) + d6449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d157, d6449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26487 p hg
    simpa only [d157, d6449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d157, d6449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26491 p hg
    simpa only [d157, d6449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26493 (p : Pattern) (guard : d6326 p = 1) : d158 p ≤ (0 : Int) + d6450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d158, d6450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26482 p hg
    simpa only [d158, d6450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d158, d6450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26492 p hg
    simpa only [d158, d6450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26494 (p : Pattern) (guard : d6326 p = 1) : d159 p ≤ (0 : Int) + d6451 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d159, d6451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26443 p hg
    simpa only [d159, d6451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d159, d6451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d159, d6451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26495 (p : Pattern) (guard : d6326 p = 1) : d160 p ≤ (0 : Int) + d6452 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d160, d6452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26494 p hg
    simpa only [d160, d6452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d160, d6452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d160, d6452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26496 (p : Pattern) (guard : d6326 p = 1) : d161 p ≤ (0 : Int) + d6453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d161, d6453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26495 p hg
    simpa only [d161, d6453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d161, d6453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d161, d6453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26497 (p : Pattern) (guard : d6326 p = 1) : d162 p ≤ (0 : Int) + d6454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d162, d6454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26496 p hg
    simpa only [d162, d6454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d162, d6454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d162, d6454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26498 (p : Pattern) (guard : d6326 p = 1) : d163 p ≤ (0 : Int) + d6455 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d163, d6455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26492 p hg
    simpa only [d163, d6455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d163, d6455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26497 p hg
    simpa only [d163, d6455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26499 (p : Pattern) (guard : d6326 p = 1) : d164 p ≤ (0 : Int) + d6456 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d164, d6456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26493 p hg
    simpa only [d164, d6456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d164, d6456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26498 p hg
    simpa only [d164, d6456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26500 (p : Pattern) (guard : d6326 p = 1) : d165 p ≤ (0 : Int) + d6457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d165, d6457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26492 p hg
    simpa only [d165, d6457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d165, d6457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d165, d6457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26501 (p : Pattern) (guard : d6326 p = 1) : d166 p ≤ (0 : Int) + d6458 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d166, d6458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26493 p hg
    simpa only [d166, d6458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d166, d6458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26500 p hg
    simpa only [d166, d6458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26502 (p : Pattern) (guard : d6326 p = 1) : d167 p ≤ (0 : Int) + d6459 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d167, d6459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26499 p hg
    simpa only [d167, d6459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d167, d6459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26501 p hg
    simpa only [d167, d6459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26503 (p : Pattern) (guard : d6326 p = 1) : d168 p ≤ (0 : Int) + d6460 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d168, d6460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26428 p hg
    simpa only [d168, d6460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d168, d6460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26502 p hg
    simpa only [d168, d6460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26504 (p : Pattern) (guard : d6326 p = 1) : d169 p ≤ (0 : Int) + d6461 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d169, d6461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26428 p hg
    simpa only [d169, d6461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d169, d6461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26503 p hg
    simpa only [d169, d6461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26505 (p : Pattern) (guard : d6326 p = 1) : d170 p ≤ (0 : Int) + d6462 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d170, d6462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26356 p hg
    simpa only [d170, d6462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d170, d6462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26363 p hg
    simpa only [d170, d6462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26506 (p : Pattern) (guard : d6326 p = 1) : d171 p ≤ (0 : Int) + d6463 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d171, d6463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26380 p hg
    simpa only [d171, d6463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d171, d6463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26505 p hg
    simpa only [d171, d6463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26507 (p : Pattern) (guard : d6326 p = 1) : d172 p ≤ (0 : Int) + d6464 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d172, d6464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26356 p hg
    simpa only [d172, d6464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d172, d6464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26368 p hg
    simpa only [d172, d6464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26508 (p : Pattern) (guard : d6326 p = 1) : d173 p ≤ (0 : Int) + d6465 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d173, d6465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26362 p hg
    simpa only [d173, d6465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d173, d6465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d173, d6465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26509 (p : Pattern) (guard : d6326 p = 1) : d174 p ≤ (0 : Int) + d6466 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d174, d6466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26507 p hg
    simpa only [d174, d6466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d174, d6466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26508 p hg
    simpa only [d174, d6466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26510 (p : Pattern) (guard : d6326 p = 1) : d175 p ≤ (0 : Int) + d6467 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d175, d6467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26506 p hg
    simpa only [d175, d6467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d175, d6467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26509 p hg
    simpa only [d175, d6467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26511 (p : Pattern) (guard : d6326 p = 1) : d176 p ≤ (0 : Int) + d6468 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d176, d6468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26393 p hg
    simpa only [d176, d6468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d176, d6468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26508 p hg
    simpa only [d176, d6468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26512 (p : Pattern) (guard : d6326 p = 1) : d177 p ≤ (0 : Int) + d6469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d177, d6469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26511 p hg
    simpa only [d177, d6469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d177, d6469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26400 p hg
    simpa only [d177, d6469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26513 (p : Pattern) (guard : d6326 p = 1) : d178 p ≤ (0 : Int) + d6470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d178, d6470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26510 p hg
    simpa only [d178, d6470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d178, d6470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26512 p hg
    simpa only [d178, d6470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26514 (p : Pattern) (guard : d6326 p = 1) : d179 p ≤ (0 : Int) + d6471 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d179, d6471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26352 p hg
    simpa only [d179, d6471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d179, d6471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26513 p hg
    simpa only [d179, d6471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26515 (p : Pattern) (guard : d6326 p = 1) : d180 p ≤ (0 : Int) + d6472 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d180, d6472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26505 p hg
    simpa only [d180, d6472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d180, d6472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26370 p hg
    simpa only [d180, d6472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26516 (p : Pattern) (guard : d6326 p = 1) : d181 p ≤ (0 : Int) + d6473 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d181, d6473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26508 p hg
    simpa only [d181, d6473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d181, d6473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26399 p hg
    simpa only [d181, d6473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26517 (p : Pattern) (guard : d6326 p = 1) : d182 p ≤ (0 : Int) + d6474 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d182, d6474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26515 p hg
    simpa only [d182, d6474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d182, d6474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26516 p hg
    simpa only [d182, d6474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26518 (p : Pattern) (guard : d6326 p = 1) : d183 p ≤ (0 : Int) + d6475 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d183, d6475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26508 p hg
    simpa only [d183, d6475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d183, d6475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d183, d6475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26519 (p : Pattern) (guard : d6326 p = 1) : d184 p ≤ (0 : Int) + d6476 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d184, d6476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26518 p hg
    simpa only [d184, d6476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d184, d6476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d184, d6476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26520 (p : Pattern) (guard : d6326 p = 1) : d185 p ≤ (0 : Int) + d6477 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d185, d6477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26517 p hg
    simpa only [d185, d6477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d185, d6477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26519 p hg
    simpa only [d185, d6477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26521 (p : Pattern) (guard : d6326 p = 1) : d186 p ≤ (0 : Int) + d6478 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d186, d6478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26392 p hg
    simpa only [d186, d6478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d186, d6478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26520 p hg
    simpa only [d186, d6478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26522 (p : Pattern) (guard : d6326 p = 1) : d187 p ≤ (0 : Int) + d6479 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d187, d6479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26514 p hg
    simpa only [d187, d6479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d187, d6479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26521 p hg
    simpa only [d187, d6479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26523 (p : Pattern) (guard : d6326 p = 1) : d188 p ≤ (0 : Int) + d6480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d188, d6480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26337 p hg
    simpa only [d188, d6480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d188, d6480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26406 p hg
    simpa only [d188, d6480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26524 (p : Pattern) (guard : d6326 p = 1) : d189 p ≤ (0 : Int) + d6481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d189, d6481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26523 p hg
    simpa only [d189, d6481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d189, d6481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26407 p hg
    simpa only [d189, d6481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26525 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26526 (p : Pattern) (guard : d6326 p = 1) : d191 p ≤ (0 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26525 p hg
    simpa only [d6326, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23785 p hg
    simpa only [d6326, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26527 (p : Pattern) (guard : d6326 p = 1) : d192 p ≤ (0 : Int) + d6482 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d192, d6482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26526 p hg
    simpa only [d192, d6482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d192, d6482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d192, d6482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26528 (p : Pattern) (guard : d6326 p = 1) : d193 p ≤ (0 : Int) + d6483 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d193, d6483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26526 p hg
    simpa only [d193, d6483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d193, d6483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26527 p hg
    simpa only [d193, d6483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26529 (p : Pattern) (guard : d6326 p = 1) : d194 p ≤ (0 : Int) + d6484 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d194, d6484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26343 p hg
    simpa only [d194, d6484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d194, d6484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26528 p hg
    simpa only [d194, d6484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26530 (p : Pattern) (guard : d6326 p = 1) : d195 p ≤ (0 : Int) + d6485 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d195, d6485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26529 p hg
    simpa only [d195, d6485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d195, d6485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d195, d6485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26531 (p : Pattern) (guard : d6326 p = 1) : d196 p ≤ (0 : Int) + d6486 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d196, d6486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26530 p hg
    simpa only [d196, d6486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d196, d6486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d196, d6486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26532 (p : Pattern) (guard : d6326 p = 1) : d197 p ≤ (0 : Int) + d6487 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d197, d6487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26524 p hg
    simpa only [d197, d6487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d197, d6487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26531 p hg
    simpa only [d197, d6487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26533 (p : Pattern) (guard : d6326 p = 1) : d198 p ≤ (0 : Int) + d6488 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d198, d6488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26343 p hg
    simpa only [d198, d6488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d198, d6488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26389 p hg
    simpa only [d198, d6488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26534 (p : Pattern) (guard : d6326 p = 1) : d199 p ≤ (0 : Int) + d6489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d199, d6489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26380 p hg
    simpa only [d199, d6489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d199, d6489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26533 p hg
    simpa only [d199, d6489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26535 (p : Pattern) (guard : d6326 p = 1) : d200 p ≤ (0 : Int) + d6490 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d200, d6490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26534 p hg
    simpa only [d200, d6490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d200, d6490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26411 p hg
    simpa only [d200, d6490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26536 (p : Pattern) (guard : d6326 p = 1) : d201 p ≤ (0 : Int) + d6491 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d201, d6491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26528 p hg
    simpa only [d201, d6491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d201, d6491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d201, d6491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26537 (p : Pattern) (guard : d6326 p = 1) : d202 p ≤ (0 : Int) + d6492 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d202, d6492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26536 p hg
    simpa only [d202, d6492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d202, d6492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d202, d6492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26538 (p : Pattern) (guard : d6326 p = 1) : d203 p ≤ (0 : Int) + d6493 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d203, d6493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26537 p hg
    simpa only [d203, d6493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d203, d6493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d203, d6493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26539 (p : Pattern) (guard : d6326 p = 1) : d204 p ≤ (0 : Int) + d6494 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d204, d6494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26535 p hg
    simpa only [d204, d6494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d204, d6494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26538 p hg
    simpa only [d204, d6494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26540 (p : Pattern) (guard : d6326 p = 1) : d205 p ≤ (0 : Int) + d6495 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d205, d6495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26532 p hg
    simpa only [d205, d6495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d205, d6495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26539 p hg
    simpa only [d205, d6495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26541 (p : Pattern) (guard : d6326 p = 1) : d206 p ≤ (0 : Int) + d6496 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d206, d6496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26522 p hg
    simpa only [d206, d6496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d206, d6496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26540 p hg
    simpa only [d206, d6496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26542 (p : Pattern) (guard : d6326 p = 1) : d207 p ≤ (0 : Int) + d6497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d207, d6497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26540 p hg
    simpa only [d207, d6497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d207, d6497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d207, d6497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26543 (p : Pattern) (guard : d6326 p = 1) : d208 p ≤ (0 : Int) + d6498 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d208, d6498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26541 p hg
    simpa only [d208, d6498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d208, d6498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26542 p hg
    simpa only [d208, d6498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26544 (p : Pattern) (guard : d6326 p = 1) : d209 p ≤ (0 : Int) + d6499 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d209, d6499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26425 p hg
    simpa only [d209, d6499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d209, d6499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26543 p hg
    simpa only [d209, d6499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26545 (p : Pattern) (guard : d6326 p = 1) : d210 p ≤ (0 : Int) + d6500 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d210, d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26428 p hg
    simpa only [d210, d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d210, d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26544 p hg
    simpa only [d210, d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26546 (p : Pattern) (guard : d6326 p = 1) : d211 p ≤ (0 : Int) + d6501 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d211, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26440 p hg
    simpa only [d211, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d211, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d211, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26547 (p : Pattern) (guard : d6326 p = 1) : d212 p ≤ (0 : Int) + d6502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d212, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26468 p hg
    simpa only [d212, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d212, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26546 p hg
    simpa only [d212, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26548 (p : Pattern) (guard : d6326 p = 1) : d213 p ≤ (0 : Int) + d6503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d213, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26546 p hg
    simpa only [d213, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d213, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d213, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26549 (p : Pattern) (guard : d6326 p = 1) : d214 p ≤ (0 : Int) + d6504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d214, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26547 p hg
    simpa only [d214, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d214, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26548 p hg
    simpa only [d214, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26550 (p : Pattern) (guard : d6326 p = 1) : d215 p ≤ (0 : Int) + d6505 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d215, d6505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26460 p hg
    simpa only [d215, d6505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d215, d6505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d215, d6505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26551 (p : Pattern) (guard : d6326 p = 1) : d216 p ≤ (0 : Int) + d6506 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d216, d6506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26475 p hg
    simpa only [d216, d6506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d216, d6506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26550 p hg
    simpa only [d216, d6506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26552 (p : Pattern) (guard : d6326 p = 1) : d217 p ≤ (0 : Int) + d6507 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d217, d6507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26550 p hg
    simpa only [d217, d6507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d217, d6507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d217, d6507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26553 (p : Pattern) (guard : d6326 p = 1) : d218 p ≤ (0 : Int) + d6508 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d218, d6508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26551 p hg
    simpa only [d218, d6508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d218, d6508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26552 p hg
    simpa only [d218, d6508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26554 (p : Pattern) (guard : d6326 p = 1) : d219 p ≤ (0 : Int) + d6509 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d219, d6509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26549 p hg
    simpa only [d219, d6509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d219, d6509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26553 p hg
    simpa only [d219, d6509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26555 (p : Pattern) (guard : d6326 p = 1) : d220 p ≤ (0 : Int) + d6510 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d220, d6510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26466 p hg
    simpa only [d220, d6510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d220, d6510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26554 p hg
    simpa only [d220, d6510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26556 (p : Pattern) (guard : d6326 p = 1) : d221 p ≤ (0 : Int) + d6511 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d221, d6511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26549 p hg
    simpa only [d221, d6511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d221, d6511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26490 p hg
    simpa only [d221, d6511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26557 (p : Pattern) (guard : d6326 p = 1) : d222 p ≤ (0 : Int) + d6512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d222, d6512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26487 p hg
    simpa only [d222, d6512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d222, d6512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26556 p hg
    simpa only [d222, d6512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26558 (p : Pattern) (guard : d6326 p = 1) : d223 p ≤ (0 : Int) + d6513 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d223, d6513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26555 p hg
    simpa only [d223, d6513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d223, d6513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26557 p hg
    simpa only [d223, d6513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26559 (p : Pattern) (guard : d6326 p = 1) : d224 p ≤ (0 : Int) + d6514 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d224, d6514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26557 p hg
    simpa only [d224, d6514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d224, d6514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26497 p hg
    simpa only [d224, d6514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26560 (p : Pattern) (guard : d6326 p = 1) : d225 p ≤ (0 : Int) + d6515 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d225, d6515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26558 p hg
    simpa only [d225, d6515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d225, d6515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26559 p hg
    simpa only [d225, d6515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26561 (p : Pattern) (guard : d6326 p = 1) : d226 p ≤ (0 : Int) + d6516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d226, d6516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26449 p hg
    simpa only [d226, d6516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d226, d6516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26456 p hg
    simpa only [d226, d6516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26562 (p : Pattern) (guard : d6326 p = 1) : d227 p ≤ (0 : Int) + d6517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d227, d6517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26467 p hg
    simpa only [d227, d6517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d227, d6517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26561 p hg
    simpa only [d227, d6517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26563 (p : Pattern) (guard : d6326 p = 1) : d228 p ≤ (0 : Int) + d6518 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d228, d6518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26562 p hg
    simpa only [d228, d6518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d228, d6518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26550 p hg
    simpa only [d228, d6518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26564 (p : Pattern) (guard : d6326 p = 1) : d229 p ≤ (0 : Int) + d6519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d229, d6519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26455 p hg
    simpa only [d229, d6519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d229, d6519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d229, d6519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26565 (p : Pattern) (guard : d6326 p = 1) : d230 p ≤ (0 : Int) + d6520 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d230, d6520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26564 p hg
    simpa only [d230, d6520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d230, d6520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d230, d6520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26566 (p : Pattern) (guard : d6326 p = 1) : d231 p ≤ (0 : Int) + d6521 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d231, d6521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26565 p hg
    simpa only [d231, d6521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d231, d6521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d231, d6521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26567 (p : Pattern) (guard : d6326 p = 1) : d232 p ≤ (0 : Int) + d6522 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d232, d6522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26563 p hg
    simpa only [d232, d6522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d232, d6522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26566 p hg
    simpa only [d232, d6522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26568 (p : Pattern) (guard : d6326 p = 1) : d233 p ≤ (0 : Int) + d6523 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d233, d6523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26445 p hg
    simpa only [d233, d6523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d233, d6523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26567 p hg
    simpa only [d233, d6523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26569 (p : Pattern) (guard : d6326 p = 1) : d234 p ≤ (0 : Int) + d6524 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d234, d6524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26438 p hg
    simpa only [d234, d6524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d234, d6524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26456 p hg
    simpa only [d234, d6524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26570 (p : Pattern) (guard : d6326 p = 1) : d235 p ≤ (0 : Int) + d6525 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d235, d6525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26569 p hg
    simpa only [d235, d6525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d235, d6525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26460 p hg
    simpa only [d235, d6525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26571 (p : Pattern) (guard : d6326 p = 1) : d236 p ≤ (0 : Int) + d6526 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d236, d6526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26570 p hg
    simpa only [d236, d6526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d236, d6526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26565 p hg
    simpa only [d236, d6526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26572 (p : Pattern) (guard : d6326 p = 1) : d237 p ≤ (0 : Int) + d6527 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d237, d6527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26376 p hg
    simpa only [d237, d6527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d237, d6527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d237, d6527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26573 (p : Pattern) (guard : d6326 p = 1) : d238 p ≤ (0 : Int) + d6528 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d238, d6528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26571 p hg
    simpa only [d238, d6528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d238, d6528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26572 p hg
    simpa only [d238, d6528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26574 (p : Pattern) (guard : d6326 p = 1) : d239 p ≤ (0 : Int) + d6529 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d239, d6529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26549 p hg
    simpa only [d239, d6529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d239, d6529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26573 p hg
    simpa only [d239, d6529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26575 (p : Pattern) (guard : d6326 p = 1) : d240 p ≤ (0 : Int) + d6530 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d240, d6530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26568 p hg
    simpa only [d240, d6530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d240, d6530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26574 p hg
    simpa only [d240, d6530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26576 (p : Pattern) (guard : d6326 p = 1) : d241 p ≤ (0 : Int) + d6531 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d241, d6531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26467 p hg
    simpa only [d241, d6531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d241, d6531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26389 p hg
    simpa only [d241, d6531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26577 (p : Pattern) (guard : d6326 p = 1) : d242 p ≤ (0 : Int) + d6532 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d242, d6532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26434 p hg
    simpa only [d242, d6532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d242, d6532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26576 p hg
    simpa only [d242, d6532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26578 (p : Pattern) (guard : d6326 p = 1) : d243 p ≤ (0 : Int) + d6533 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d243, d6533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26577 p hg
    simpa only [d243, d6533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d243, d6533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26472 p hg
    simpa only [d243, d6533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26579 (p : Pattern) (guard : d6326 p = 1) : d244 p ≤ (0 : Int) + d6534 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d244, d6534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26578 p hg
    simpa only [d244, d6534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d244, d6534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26490 p hg
    simpa only [d244, d6534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26580 (p : Pattern) (guard : d6326 p = 1) : d245 p ≤ (0 : Int) + d6535 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d245, d6535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26467 p hg
    simpa only [d245, d6535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d245, d6535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26546 p hg
    simpa only [d245, d6535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26581 (p : Pattern) (guard : d6326 p = 1) : d246 p ≤ (0 : Int) + d6536 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d246, d6536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26580 p hg
    simpa only [d246, d6536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d246, d6536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26489 p hg
    simpa only [d246, d6536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26582 (p : Pattern) (guard : d6326 p = 1) : d247 p ≤ (0 : Int) + d6537 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d247, d6537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26350 p hg
    simpa only [d247, d6537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d247, d6537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d247, d6537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26583 (p : Pattern) (guard : d6326 p = 1) : d248 p ≤ (0 : Int) + d6538 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d248, d6538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26582 p hg
    simpa only [d248, d6538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d248, d6538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d248, d6538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26584 (p : Pattern) (guard : d6326 p = 1) : d249 p ≤ (0 : Int) + d6539 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d249, d6539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26581 p hg
    simpa only [d249, d6539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d249, d6539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26583 p hg
    simpa only [d249, d6539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26585 (p : Pattern) (guard : d6326 p = 1) : d250 p ≤ (0 : Int) + d6540 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d250, d6540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26579 p hg
    simpa only [d250, d6540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d250, d6540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26584 p hg
    simpa only [d250, d6540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26586 (p : Pattern) (guard : d6326 p = 1) : d251 p ≤ (0 : Int) + d6541 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d251, d6541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26575 p hg
    simpa only [d251, d6541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d251, d6541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26585 p hg
    simpa only [d251, d6541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26587 (p : Pattern) (guard : d6326 p = 1) : d252 p ≤ (0 : Int) + d6542 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d252, d6542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26467 p hg
    simpa only [d252, d6542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d252, d6542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26349 p hg
    simpa only [d252, d6542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26588 (p : Pattern) (guard : d6326 p = 1) : d253 p ≤ (0 : Int) + d6543 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d253, d6543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26434 p hg
    simpa only [d253, d6543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d253, d6543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26587 p hg
    simpa only [d253, d6543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26589 (p : Pattern) (guard : d6326 p = 1) : d254 p ≤ (0 : Int) + d6544 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d254, d6544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26440 p hg
    simpa only [d254, d6544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d254, d6544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26349 p hg
    simpa only [d254, d6544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26590 (p : Pattern) (guard : d6326 p = 1) : d255 p ≤ (0 : Int) + d6545 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d255, d6545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26589 p hg
    simpa only [d255, d6545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d255, d6545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d255, d6545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26591 (p : Pattern) (guard : d6326 p = 1) : d256 p ≤ (0 : Int) + d6546 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d256, d6546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26588 p hg
    simpa only [d256, d6546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d256, d6546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26590 p hg
    simpa only [d256, d6546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26592 (p : Pattern) (guard : d6326 p = 1) : d257 p ≤ (0 : Int) + d6547 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d257, d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26483 p hg
    simpa only [d257, d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d257, d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26389 p hg
    simpa only [d257, d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26593 (p : Pattern) (guard : d6326 p = 1) : d258 p ≤ (0 : Int) + d6548 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d258, d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26592 p hg
    simpa only [d258, d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d258, d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d258, d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26594 (p : Pattern) (guard : d6326 p = 1) : d259 p ≤ (0 : Int) + d6549 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d259, d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26593 p hg
    simpa only [d259, d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d259, d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d259, d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26595 (p : Pattern) (guard : d6326 p = 1) : d260 p ≤ (0 : Int) + d6550 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d260, d6550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26591 p hg
    simpa only [d260, d6550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d260, d6550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26594 p hg
    simpa only [d260, d6550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26596 (p : Pattern) (guard : d6326 p = 1) : d261 p ≤ (0 : Int) + d6551 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d261, d6551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26595 p hg
    simpa only [d261, d6551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d261, d6551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26584 p hg
    simpa only [d261, d6551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26597 (p : Pattern) (guard : d6326 p = 1) : d262 p ≤ (0 : Int) + d6552 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d262, d6552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26596 p hg
    simpa only [d262, d6552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d262, d6552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26335 p hg
    simpa only [d262, d6552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26598 (p : Pattern) (guard : d6326 p = 1) : d263 p ≤ (0 : Int) + d6553 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d263, d6553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26586 p hg
    simpa only [d263, d6553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d263, d6553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26597 p hg
    simpa only [d263, d6553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26599 (p : Pattern) (guard : d6326 p = 1) : d264 p ≤ (0 : Int) + d6554 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d264, d6554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26560 p hg
    simpa only [d264, d6554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d264, d6554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26598 p hg
    simpa only [d264, d6554, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
