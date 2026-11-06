import NetHack.Soko22Hazard87.Compare193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48500 (p : Pattern) (guard : d369653 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369652 p = 1 := by simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48499 p hg
    simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48501 (p : Pattern) (guard : d369654 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369653 p = 1 := by simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48500 p hg
    simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48502 (p : Pattern) (guard : d369655 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369644 p = 1 := by simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48493 p hg
    simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369654 p = 1 := by simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48501 p hg
    simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48503 (p : Pattern) (guard : d369656 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369645 p = 1 := by simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48494 p hg
    simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369655 p = 1 := by simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48502 p hg
    simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48504 (p : Pattern) (guard : d369657 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369656 p = 1 := by simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48503 p hg
    simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48505 (p : Pattern) (guard : d370495 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369657 p = 1 := by simpa only [d370495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48504 p hg
    simpa only [d370495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48506 (p : Pattern) (guard : d370496 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370495 p = 1 := by simpa only [d370496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48505 p hg
    simpa only [d370496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48507 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (0 : Int) + d49561 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48508 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (0 : Int) + d47705 p := by
  have ha := bounds5 p
  have hb := bounds47705 p
  omega
theorem compare48509 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48510 (p : Pattern) (guard : d15 p = 1) : d47706 p ≤ (0 : Int) + d47947 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48508 p hg
    simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48509 p hg
    simpa only [d15, d47706, d47947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48511 (p : Pattern) (guard : d45587 p = 1) : d47706 p ≤ (0 : Int) + d47947 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48319 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48510 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48512 (p : Pattern) (guard : d46040 p = 1) : d47706 p ≤ (0 : Int) + d49564 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48314 p hg
    simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48511 p hg
    simpa only [d46040, d49564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48513 (p : Pattern) (guard : d46041 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48507 p hg
    simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48512 p hg
    simpa only [d46041, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48514 (p : Pattern) (guard : d46042 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48513 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48515 (p : Pattern) (guard : d46043 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48514 p hg
    simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48134 p hg
    simpa only [d46043, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48516 (p : Pattern) (guard : d369497 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48515 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48323 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48517 (p : Pattern) (guard : d46459 p = 1) : d47706 p ≤ (0 : Int) + d49561 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48308 p hg
    simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48129 p hg
    simpa only [d46459, d49561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48518 (p : Pattern) (guard : d46460 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48517 p hg
    simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48131 p hg
    simpa only [d46460, d49565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48519 (p : Pattern) (guard : d369498 p = 1) : d47706 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48518 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48520 (p : Pattern) (guard : d369499 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48519 p hg
    simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48134 p hg
    simpa only [d369499, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48521 (p : Pattern) (guard : d369500 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48520 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48135 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48522 (p : Pattern) (guard : d369501 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48516 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48521 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48523 (p : Pattern) (guard : d369502 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48522 p hg
    simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d369502, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48524 (p : Pattern) (guard : d369503 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48523 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48326 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48525 (p : Pattern) (guard : d369504 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48524 p hg
    simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369504, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48526 (p : Pattern) (guard : d369505 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369504 p = 1 := by simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48525 p hg
    simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369505, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48527 (p : Pattern) (guard : d369506 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369505 p = 1 := by simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48526 p hg
    simpa only [d369506, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48528 (p : Pattern) (guard : d369507 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369506 p = 1 := by simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48527 p hg
    simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d369507, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48529 (p : Pattern) (guard : d369508 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48528 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369394 p = 1 := by simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48331 p hg
    simpa only [d369508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48530 (p : Pattern) (guard : d369509 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48324 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48531 (p : Pattern) (guard : d369510 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48530 p hg
    simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d369510, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48532 (p : Pattern) (guard : d369511 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48531 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48139 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48533 (p : Pattern) (guard : d369512 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48532 p hg
    simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369512, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48534 (p : Pattern) (guard : d369513 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369512 p = 1 := by simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48533 p hg
    simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369513, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48535 (p : Pattern) (guard : d369514 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369513 p = 1 := by simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48534 p hg
    simpa only [d369514, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48536 (p : Pattern) (guard : d369515 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369514 p = 1 := by simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48535 p hg
    simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d369515, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48537 (p : Pattern) (guard : d369516 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369515 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48536 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275508 p = 1 := by simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48147 p hg
    simpa only [d369516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48538 (p : Pattern) (guard : d369517 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369508 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48529 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369516 p = 1 := by simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48537 p hg
    simpa only [d369517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48539 (p : Pattern) (guard : d369518 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369517 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48538 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369396 p = 1 := by simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48333 p hg
    simpa only [d369518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48540 (p : Pattern) (guard : d369519 p = 1) : d50664 p ≤ (0 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48126 p hg
    simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369518 p = 1 := by simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48539 p hg
    simpa only [d369519, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48541 (p : Pattern) (guard : d369520 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369519 p = 1 := by simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48540 p hg
    simpa only [d369520, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48542 (p : Pattern) (guard : d369521 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369520 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48541 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369399 p = 1 := by simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48336 p hg
    simpa only [d369521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48543 (p : Pattern) (guard : d369623 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48336 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48544 (p : Pattern) (guard : d369624 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369521 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48542 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369623 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48543 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48545 (p : Pattern) (guard : d369625 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369624 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48544 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48546 (p : Pattern) (guard : d369626 p = 1) : d50673 p ≤ (0 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369625 p = 1 := by simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48545 p hg
    simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48158 p hg
    simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48547 (p : Pattern) (guard : d369627 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48124 p hg
    simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369626 p = 1 := by simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48546 p hg
    simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48548 (p : Pattern) (guard : d369628 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369623 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48543 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48549 (p : Pattern) (guard : d369629 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369628 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48548 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48550 (p : Pattern) (guard : d369630 p = 1) : d50673 p ≤ (0 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369629 p = 1 := by simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48549 p hg
    simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48158 p hg
    simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48551 (p : Pattern) (guard : d369631 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48124 p hg
    simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369630 p = 1 := by simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48550 p hg
    simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48552 (p : Pattern) (guard : d369632 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369627 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48547 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369631 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48551 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48553 (p : Pattern) (guard : d369633 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369632 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48552 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48554 (p : Pattern) (guard : d369634 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369633 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48553 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48555 (p : Pattern) (guard : d369648 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369634 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48554 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48556 (p : Pattern) (guard : d369636 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369631 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48551 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48557 (p : Pattern) (guard : d369637 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369636 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48556 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48558 (p : Pattern) (guard : d369638 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369637 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48557 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48559 (p : Pattern) (guard : d369649 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369638 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48558 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48560 (p : Pattern) (guard : d369650 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369648 p = 1 := by simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48555 p hg
    simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369649 p = 1 := by simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48559 p hg
    simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48561 (p : Pattern) (guard : d369651 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369650 p = 1 := by simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48560 p hg
    simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48562 (p : Pattern) (guard : d369652 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369651 p = 1 := by simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48561 p hg
    simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48563 (p : Pattern) (guard : d369653 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369652 p = 1 := by simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48562 p hg
    simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48564 (p : Pattern) (guard : d369654 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369653 p = 1 := by simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48563 p hg
    simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48565 (p : Pattern) (guard : d370497 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370497, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370497, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369654 p = 1 := by simpa only [d370497, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48564 p hg
    simpa only [d370497, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48566 (p : Pattern) (guard : d370498 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370497 p = 1 := by simpa only [d370498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48565 p hg
    simpa only [d370498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48567 (p : Pattern) (guard : d370499 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370498 p = 1 := by simpa only [d370499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48566 p hg
    simpa only [d370499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48568 (p : Pattern) (guard : d370500 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370499 p = 1 := by simpa only [d370500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48567 p hg
    simpa only [d370500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48569 (p : Pattern) (guard : d370501 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370500 p = 1 := by simpa only [d370501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48568 p hg
    simpa only [d370501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48570 (p : Pattern) (guard : d370502 p = 1) : d50676 p ≤ (0 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370496 p = 1 := by simpa only [d370502, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48506 p hg
    simpa only [d370502, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370501 p = 1 := by simpa only [d370502, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48569 p hg
    simpa only [d370502, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48571 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d49311 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48572 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (0 : Int) + d47629 p := by
  have ha := bounds2 p
  have hb := bounds47629 p
  omega
theorem compare48573 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (0 : Int) + d47638 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48574 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (0 : Int) + d49314 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48572 p hg
    simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48573 p hg
    simpa only [d15, d47630, d49314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48575 (p : Pattern) (guard : d45587 p = 1) : d47630 p ≤ (0 : Int) + d49314 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48368 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48574 p hg
    simpa only [d45587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48576 (p : Pattern) (guard : d46040 p = 1) : d47630 p ≤ (0 : Int) + d49315 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48363 p hg
    simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48575 p hg
    simpa only [d46040, d49315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48577 (p : Pattern) (guard : d46041 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48571 p hg
    simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48576 p hg
    simpa only [d46041, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48578 (p : Pattern) (guard : d46042 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48577 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48579 (p : Pattern) (guard : d46043 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48578 p hg
    simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48187 p hg
    simpa only [d46043, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48580 (p : Pattern) (guard : d369497 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48579 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48372 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48581 (p : Pattern) (guard : d46459 p = 1) : d47630 p ≤ (0 : Int) + d49311 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48357 p hg
    simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48182 p hg
    simpa only [d46459, d49311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48582 (p : Pattern) (guard : d46460 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48581 p hg
    simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48184 p hg
    simpa only [d46460, d49316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48583 (p : Pattern) (guard : d369498 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48582 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48584 (p : Pattern) (guard : d369499 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48583 p hg
    simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48187 p hg
    simpa only [d369499, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48585 (p : Pattern) (guard : d369500 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48584 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48188 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48586 (p : Pattern) (guard : d369501 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48580 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48585 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48587 (p : Pattern) (guard : d369502 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48586 p hg
    simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d369502, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48588 (p : Pattern) (guard : d369503 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48587 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48375 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48589 (p : Pattern) (guard : d369575 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369503 p = 1 := by simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48588 p hg
    simpa only [d369575, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48590 (p : Pattern) (guard : d369504 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48453 p hg
    simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369504, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48591 (p : Pattern) (guard : d369576 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369575 p = 1 := by simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48589 p hg
    simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369504 p = 1 := by simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48590 p hg
    simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48592 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (0 : Int) + d49319 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48593 (p : Pattern) (guard : d46040 p = 1) : d47634 p ≤ (0 : Int) + d49322 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48386 p hg
    simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48384 p hg
    simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48594 (p : Pattern) (guard : d46041 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48592 p hg
    simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48593 p hg
    simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48595 (p : Pattern) (guard : d46042 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48594 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48596 (p : Pattern) (guard : d46043 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48595 p hg
    simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48204 p hg
    simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48597 (p : Pattern) (guard : d369497 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48596 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48394 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48598 (p : Pattern) (guard : d46459 p = 1) : d47634 p ≤ (0 : Int) + d49319 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48380 p hg
    simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48199 p hg
    simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48599 (p : Pattern) (guard : d46460 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48598 p hg
    simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48201 p hg
    simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48600 (p : Pattern) (guard : d369498 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48599 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48601 (p : Pattern) (guard : d369499 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48600 p hg
    simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48204 p hg
    simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48602 (p : Pattern) (guard : d369500 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48601 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48205 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48603 (p : Pattern) (guard : d369501 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48597 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48602 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48604 (p : Pattern) (guard : d369502 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48603 p hg
    simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48605 (p : Pattern) (guard : d369503 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48604 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48397 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48606 (p : Pattern) (guard : d369504 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48605 p hg
    simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48607 (p : Pattern) (guard : d369505 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369504 p = 1 := by simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48606 p hg
    simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48608 (p : Pattern) (guard : d369577 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369576 p = 1 := by simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48591 p hg
    simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369505 p = 1 := by simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48607 p hg
    simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48609 (p : Pattern) (guard : d369578 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369577 p = 1 := by simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48608 p hg
    simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48610 (p : Pattern) (guard : d369579 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369578 p = 1 := by simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48609 p hg
    simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369437 p = 1 := by simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48402 p hg
    simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48611 (p : Pattern) (guard : d369509 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48373 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48612 (p : Pattern) (guard : d369510 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48611 p hg
    simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48613 (p : Pattern) (guard : d369511 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48612 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48192 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48614 (p : Pattern) (guard : d369580 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369511 p = 1 := by simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48613 p hg
    simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48615 (p : Pattern) (guard : d369512 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48616 (p : Pattern) (guard : d369581 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369580 p = 1 := by simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48614 p hg
    simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369512 p = 1 := by simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48615 p hg
    simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48617 (p : Pattern) (guard : d369509 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48395 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48618 (p : Pattern) (guard : d369510 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48617 p hg
    simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48619 (p : Pattern) (guard : d369511 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48618 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48209 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48620 (p : Pattern) (guard : d369512 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48619 p hg
    simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48621 (p : Pattern) (guard : d369513 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369512 p = 1 := by simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48620 p hg
    simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48622 (p : Pattern) (guard : d369582 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369581 p = 1 := by simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48616 p hg
    simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369513 p = 1 := by simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48621 p hg
    simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48623 (p : Pattern) (guard : d369583 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369582 p = 1 := by simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48622 p hg
    simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48624 (p : Pattern) (guard : d369584 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369583 p = 1 := by simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48623 p hg
    simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275549 p = 1 := by simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48216 p hg
    simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48625 (p : Pattern) (guard : d369585 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369579 p = 1 := by simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48610 p hg
    simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369584 p = 1 := by simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48624 p hg
    simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48626 (p : Pattern) (guard : d369586 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369585 p = 1 := by simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48625 p hg
    simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369439 p = 1 := by simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48404 p hg
    simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48627 (p : Pattern) (guard : d369587 p = 1) : d50734 p ≤ (0 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48179 p hg
    simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369586 p = 1 := by simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48626 p hg
    simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48628 (p : Pattern) (guard : d369588 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48178 p hg
    simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369587 p = 1 := by simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48627 p hg
    simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48629 (p : Pattern) (guard : d369589 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369588 p = 1 := by simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48628 p hg
    simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369442 p = 1 := by simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48407 p hg
    simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48630 (p : Pattern) (guard : d369801 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369442 p = 1 := by simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48407 p hg
    simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48631 (p : Pattern) (guard : d369802 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369589 p = 1 := by simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48629 p hg
    simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369801 p = 1 := by simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48630 p hg
    simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48632 (p : Pattern) (guard : d369803 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369802 p = 1 := by simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48631 p hg
    simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48633 (p : Pattern) (guard : d369804 p = 1) : d50737 p ≤ (0 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369803 p = 1 := by simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48632 p hg
    simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48227 p hg
    simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48634 (p : Pattern) (guard : d369805 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369804 p = 1 := by simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48633 p hg
    simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48635 (p : Pattern) (guard : d369810 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369801 p = 1 := by simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48630 p hg
    simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48636 (p : Pattern) (guard : d369811 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369810 p = 1 := by simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48635 p hg
    simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48637 (p : Pattern) (guard : d369812 p = 1) : d50737 p ≤ (0 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369811 p = 1 := by simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48636 p hg
    simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48227 p hg
    simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48638 (p : Pattern) (guard : d369813 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369812 p = 1 := by simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48637 p hg
    simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48639 (p : Pattern) (guard : d369814 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369805 p = 1 := by simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48634 p hg
    simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369813 p = 1 := by simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48638 p hg
    simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48640 (p : Pattern) (guard : d369815 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369814 p = 1 := by simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48639 p hg
    simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48641 (p : Pattern) (guard : d369816 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369815 p = 1 := by simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48640 p hg
    simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48642 (p : Pattern) (guard : d369817 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369816 p = 1 := by simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48641 p hg
    simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48643 (p : Pattern) (guard : d369831 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369813 p = 1 := by simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48638 p hg
    simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48644 (p : Pattern) (guard : d369832 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369831 p = 1 := by simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48643 p hg
    simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48645 (p : Pattern) (guard : d369833 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369832 p = 1 := by simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48644 p hg
    simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48646 (p : Pattern) (guard : d369834 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369833 p = 1 := by simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48645 p hg
    simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48647 (p : Pattern) (guard : d370503 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369817 p = 1 := by simpa only [d370503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48642 p hg
    simpa only [d370503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369834 p = 1 := by simpa only [d370503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48646 p hg
    simpa only [d370503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48648 (p : Pattern) (guard : d370504 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370503 p = 1 := by simpa only [d370504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48647 p hg
    simpa only [d370504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48649 (p : Pattern) (guard : d370505 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d370504 p = 1 := by simpa only [d370505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48648 p hg
    simpa only [d370505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48650 (p : Pattern) (guard : d370506 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370505 p = 1 := by simpa only [d370506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48649 p hg
    simpa only [d370506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48651 (p : Pattern) (guard : d370507 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370506 p = 1 := by simpa only [d370507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48650 p hg
    simpa only [d370507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48652 (p : Pattern) (guard : d370508 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370508, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370508, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370507 p = 1 := by simpa only [d370508, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48651 p hg
    simpa only [d370508, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48653 (p : Pattern) (guard : d370509 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370508 p = 1 := by simpa only [d370509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48652 p hg
    simpa only [d370509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48654 (p : Pattern) (guard : d370510 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370509 p = 1 := by simpa only [d370510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48653 p hg
    simpa only [d370510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48655 (p : Pattern) (guard : d370511 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370510 p = 1 := by simpa only [d370511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48654 p hg
    simpa only [d370511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48656 (p : Pattern) (guard : d370512 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370511 p = 1 := by simpa only [d370512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48655 p hg
    simpa only [d370512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48657 (p : Pattern) (guard : d370513 p = 1) : d50822 p ≤ (0 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370512 p = 1 := by simpa only [d370513, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48656 p hg
    simpa only [d370513, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370513, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48244 p hg
    simpa only [d370513, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48658 (p : Pattern) (guard : d370514 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d370502 p = 1 := by simpa only [d370514, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48570 p hg
    simpa only [d370514, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370513 p = 1 := by simpa only [d370514, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48657 p hg
    simpa only [d370514, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48659 (p : Pattern) (guard : d370515 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370514 p = 1 := by simpa only [d370515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48658 p hg
    simpa only [d370515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48660 (p : Pattern) (guard : d370516 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370515 p = 1 := by simpa only [d370516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48659 p hg
    simpa only [d370516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48661 (p : Pattern) (guard : d370517 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370516 p = 1 := by simpa only [d370517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48660 p hg
    simpa only [d370517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48662 (p : Pattern) (guard : d370518 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370517 p = 1 := by simpa only [d370518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48661 p hg
    simpa only [d370518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48663 (p : Pattern) (guard : d370519 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370518 p = 1 := by simpa only [d370519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48662 p hg
    simpa only [d370519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48664 (p : Pattern) (guard : d370520 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370519 p = 1 := by simpa only [d370520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48663 p hg
    simpa only [d370520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48665 (p : Pattern) (guard : d370521 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370520 p = 1 := by simpa only [d370521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48664 p hg
    simpa only [d370521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48666 (p : Pattern) (guard : d370522 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d370494 p = 1 := by simpa only [d370522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48435 p hg
    simpa only [d370522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370521 p = 1 := by simpa only [d370522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48665 p hg
    simpa only [d370522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48667 (p : Pattern) (guard : d46053 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48444 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48668 (p : Pattern) (guard : d46054 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48667 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48669 (p : Pattern) (guard : d46055 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48668 p hg
    simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48670 (p : Pattern) (guard : d179205 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48074 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48671 (p : Pattern) (guard : d369676 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48445 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48670 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48672 (p : Pattern) (guard : d369677 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48671 p hg
    simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48673 (p : Pattern) (guard : d369678 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48669 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48672 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48674 (p : Pattern) (guard : d369679 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48673 p hg
    simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48675 (p : Pattern) (guard : d369680 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369679 p = 1 := by simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48674 p hg
    simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48676 (p : Pattern) (guard : d369681 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369680 p = 1 := by simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48675 p hg
    simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48677 (p : Pattern) (guard : d369682 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369681 p = 1 := by simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48676 p hg
    simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48678 (p : Pattern) (guard : d369683 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48452 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48460 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48679 (p : Pattern) (guard : d369684 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48678 p hg
    simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48680 (p : Pattern) (guard : d369685 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369684 p = 1 := by simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48679 p hg
    simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48681 (p : Pattern) (guard : d369686 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369685 p = 1 := by simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48680 p hg
    simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48682 (p : Pattern) (guard : d369687 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369686 p = 1 := by simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48681 p hg
    simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48683 (p : Pattern) (guard : d369688 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369682 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48677 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369687 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48682 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48684 (p : Pattern) (guard : d369689 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48445 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48685 (p : Pattern) (guard : d369690 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48684 p hg
    simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48077 p hg
    simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48686 (p : Pattern) (guard : d369691 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48685 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48460 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48687 (p : Pattern) (guard : d369692 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48686 p hg
    simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48688 (p : Pattern) (guard : d369693 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369692 p = 1 := by simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48687 p hg
    simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48689 (p : Pattern) (guard : d369694 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369693 p = 1 := by simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48688 p hg
    simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48690 (p : Pattern) (guard : d369695 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369694 p = 1 := by simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48689 p hg
    simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48691 (p : Pattern) (guard : d369855 p = 1) : d50553 p ≤ (0 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48271 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48079 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48692 (p : Pattern) (guard : d369856 p = 1) : d50570 p ≤ (0 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48691 p hg
    simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48081 p hg
    simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48693 (p : Pattern) (guard : d369857 p = 1) : d50571 p ≤ (0 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369856 p = 1 := by simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48692 p hg
    simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48083 p hg
    simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48694 (p : Pattern) (guard : d369858 p = 1) : d50572 p ≤ (0 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48066 p hg
    simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369857 p = 1 := by simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48693 p hg
    simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48695 (p : Pattern) (guard : d369859 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369858 p = 1 := by simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48694 p hg
    simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48086 p hg
    simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48696 (p : Pattern) (guard : d369860 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369695 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48690 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48695 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48697 (p : Pattern) (guard : d369861 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369688 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48683 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369860 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48696 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48698 (p : Pattern) (guard : d369862 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48457 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48695 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48699 (p : Pattern) (guard : d369863 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369859 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48695 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48088 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48700 (p : Pattern) (guard : d369864 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369862 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48698 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369863 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48699 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48701 (p : Pattern) (guard : d369865 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369861 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48697 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369864 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48700 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48702 (p : Pattern) (guard : d369866 p = 1) : d50577 p ≤ (0 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48065 p hg
    simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369865 p = 1 := by simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48701 p hg
    simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48703 (p : Pattern) (guard : d369867 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48064 p hg
    simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369866 p = 1 := by simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48702 p hg
    simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48704 (p : Pattern) (guard : d369868 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369863 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48699 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48088 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48705 (p : Pattern) (guard : d369869 p = 1) : d50576 p ≤ (0 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369864 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48700 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369868 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48704 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48706 (p : Pattern) (guard : d369870 p = 1) : d50577 p ≤ (0 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48065 p hg
    simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369869 p = 1 := by simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48705 p hg
    simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48707 (p : Pattern) (guard : d369871 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48064 p hg
    simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369870 p = 1 := by simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48706 p hg
    simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48708 (p : Pattern) (guard : d369872 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369867 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48703 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369871 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48707 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48709 (p : Pattern) (guard : d369873 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369871 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48707 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48710 (p : Pattern) (guard : d369874 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369872 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48708 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369873 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48709 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48711 (p : Pattern) (guard : d369875 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369874 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48710 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48712 (p : Pattern) (guard : d369876 p = 1) : d50590 p ≤ (0 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369875 p = 1 := by simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48711 p hg
    simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48098 p hg
    simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48713 (p : Pattern) (guard : d369877 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369876 p = 1 := by simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48712 p hg
    simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48714 (p : Pattern) (guard : d369878 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369873 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48709 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48715 (p : Pattern) (guard : d369879 p = 1) : d50578 p ≤ (0 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369878 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48714 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48094 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48716 (p : Pattern) (guard : d369880 p = 1) : d50590 p ≤ (0 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369879 p = 1 := by simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48715 p hg
    simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48098 p hg
    simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48717 (p : Pattern) (guard : d369881 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369880 p = 1 := by simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48716 p hg
    simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48718 (p : Pattern) (guard : d369882 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369877 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48713 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369881 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48717 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48719 (p : Pattern) (guard : d369883 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369882 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48718 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48720 (p : Pattern) (guard : d369884 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369883 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48719 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48721 (p : Pattern) (guard : d369885 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369884 p = 1 := by simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48720 p hg
    simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48722 (p : Pattern) (guard : d369886 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369881 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48717 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48723 (p : Pattern) (guard : d369887 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369886 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48722 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48724 (p : Pattern) (guard : d369888 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369887 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48723 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48725 (p : Pattern) (guard : d369889 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369888 p = 1 := by simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48724 p hg
    simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48726 (p : Pattern) (guard : d369890 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369885 p = 1 := by simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48721 p hg
    simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369889 p = 1 := by simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48725 p hg
    simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48727 (p : Pattern) (guard : d369891 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369890 p = 1 := by simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48726 p hg
    simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48728 (p : Pattern) (guard : d369892 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369891 p = 1 := by simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48727 p hg
    simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48729 (p : Pattern) (guard : d369893 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369892 p = 1 := by simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48728 p hg
    simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48730 (p : Pattern) (guard : d369894 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369893 p = 1 := by simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48729 p hg
    simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48731 (p : Pattern) (guard : d369895 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369894 p = 1 := by simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48730 p hg
    simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48732 (p : Pattern) (guard : d369898 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369884 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48720 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48733 (p : Pattern) (guard : d369899 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369888 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48724 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48734 (p : Pattern) (guard : d369900 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369898 p = 1 := by simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48732 p hg
    simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369899 p = 1 := by simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48733 p hg
    simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48735 (p : Pattern) (guard : d369901 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369900 p = 1 := by simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48734 p hg
    simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48736 (p : Pattern) (guard : d369902 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369901 p = 1 := by simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48735 p hg
    simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48737 (p : Pattern) (guard : d369903 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369902 p = 1 := by simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48736 p hg
    simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48738 (p : Pattern) (guard : d369904 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369903 p = 1 := by simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48737 p hg
    simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48739 (p : Pattern) (guard : d369905 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369894 p = 1 := by simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48730 p hg
    simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369904 p = 1 := by simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48738 p hg
    simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48740 (p : Pattern) (guard : d369906 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369895 p = 1 := by simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48731 p hg
    simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369905 p = 1 := by simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48739 p hg
    simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48741 (p : Pattern) (guard : d369907 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369906 p = 1 := by simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48740 p hg
    simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48742 (p : Pattern) (guard : d370523 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369907 p = 1 := by simpa only [d370523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48741 p hg
    simpa only [d370523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48743 (p : Pattern) (guard : d370524 p = 1) : d50591 p ≤ (0 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370523 p = 1 := by simpa only [d370524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48742 p hg
    simpa only [d370524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48744 (p : Pattern) (guard : d46053 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48515 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48745 (p : Pattern) (guard : d46054 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48744 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48746 (p : Pattern) (guard : d46055 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48745 p hg
    simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48747 (p : Pattern) (guard : d179205 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48135 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48748 (p : Pattern) (guard : d369676 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48516 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48747 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48749 (p : Pattern) (guard : d369677 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48748 p hg
    simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
