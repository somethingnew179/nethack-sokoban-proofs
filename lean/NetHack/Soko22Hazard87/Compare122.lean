import NetHack.Soko22Hazard87.Compare121
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30500 (p : Pattern) (guard : d259580 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30499 p hg
    simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30501 (p : Pattern) (guard : d259581 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30500 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30502 (p : Pattern) (guard : d259582 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30501 p hg
    simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30503 (p : Pattern) (guard : d259583 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259582 p = 1 := by simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30502 p hg
    simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30504 (p : Pattern) (guard : d259584 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259583 p = 1 := by simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30503 p hg
    simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30505 (p : Pattern) (guard : d259585 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259584 p = 1 := by simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30504 p hg
    simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30506 (p : Pattern) (guard : d259586 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258189 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30055 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259585 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30505 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30507 (p : Pattern) (guard : d259666 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258476 p = 1 := by simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30492 p hg
    simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259586 p = 1 := by simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30506 p hg
    simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30508 (p : Pattern) (guard : d259587 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30500 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28976 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30509 (p : Pattern) (guard : d259588 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30508 p hg
    simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30510 (p : Pattern) (guard : d259589 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259588 p = 1 := by simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30509 p hg
    simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30511 (p : Pattern) (guard : d259590 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259589 p = 1 := by simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30510 p hg
    simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30512 (p : Pattern) (guard : d259591 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259590 p = 1 := by simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30511 p hg
    simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30513 (p : Pattern) (guard : d259592 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30505 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259591 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30512 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30514 (p : Pattern) (guard : d259593 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259586 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30506 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259592 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30513 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30515 (p : Pattern) (guard : d259667 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259666 p = 1 := by simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30507 p hg
    simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259593 p = 1 := by simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30514 p hg
    simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30516 (p : Pattern) (guard : d259668 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259668, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259668, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259667 p = 1 := by simpa only [d259668, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30515 p hg
    simpa only [d259668, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30517 (p : Pattern) (guard : d259669 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259669, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259669, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259668 p = 1 := by simpa only [d259669, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30516 p hg
    simpa only [d259669, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30518 (p : Pattern) (guard : d259602 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259591 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30512 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30519 (p : Pattern) (guard : d259670 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259592 p = 1 := by simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30513 p hg
    simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259602 p = 1 := by simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30518 p hg
    simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30520 (p : Pattern) (guard : d259671 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259593 p = 1 := by simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30514 p hg
    simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259670 p = 1 := by simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30519 p hg
    simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30521 (p : Pattern) (guard : d259672 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259672, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259672, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259671 p = 1 := by simpa only [d259672, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30520 p hg
    simpa only [d259672, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30522 (p : Pattern) (guard : d259673 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259673, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259673, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259672 p = 1 := by simpa only [d259673, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30521 p hg
    simpa only [d259673, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30523 (p : Pattern) (guard : d259674 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259669 p = 1 := by simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30517 p hg
    simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259673 p = 1 := by simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30522 p hg
    simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30524 (p : Pattern) (guard : d259594 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30498 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30073 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30525 (p : Pattern) (guard : d259595 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30524 p hg
    simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30526 (p : Pattern) (guard : d259596 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30525 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28976 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30527 (p : Pattern) (guard : d259597 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30526 p hg
    simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30528 (p : Pattern) (guard : d259598 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259597 p = 1 := by simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30527 p hg
    simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30529 (p : Pattern) (guard : d259599 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259598 p = 1 := by simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30528 p hg
    simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30530 (p : Pattern) (guard : d259600 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259599 p = 1 := by simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30529 p hg
    simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30531 (p : Pattern) (guard : d259601 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30505 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259600 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30532 (p : Pattern) (guard : d259603 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259601 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30531 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259602 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30518 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30533 (p : Pattern) (guard : d259604 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259593 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30514 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259603 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30532 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30534 (p : Pattern) (guard : d259605 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259604 p = 1 := by simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30533 p hg
    simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30535 (p : Pattern) (guard : d259606 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259605 p = 1 := by simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30534 p hg
    simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30536 (p : Pattern) (guard : d259607 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259600 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30530 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30537 (p : Pattern) (guard : d259608 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259607 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30536 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30538 (p : Pattern) (guard : d259609 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259603 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30532 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259608 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30537 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30539 (p : Pattern) (guard : d259610 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259609 p = 1 := by simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30538 p hg
    simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30540 (p : Pattern) (guard : d259611 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259610 p = 1 := by simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30539 p hg
    simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30541 (p : Pattern) (guard : d259612 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259606 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30535 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259611 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30540 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30542 (p : Pattern) (guard : d259675 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259674 p = 1 := by simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30523 p hg
    simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259612 p = 1 := by simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30541 p hg
    simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30543 (p : Pattern) (guard : d259676 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259675 p = 1 := by simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30542 p hg
    simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30544 (p : Pattern) (guard : d259677 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259676 p = 1 := by simpa only [d259677, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30543 p hg
    simpa only [d259677, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259677, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259677, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30545 (p : Pattern) (guard : d259678 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259678, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259678, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259677 p = 1 := by simpa only [d259678, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30544 p hg
    simpa only [d259678, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30546 (p : Pattern) (guard : d259613 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259611 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30540 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30547 (p : Pattern) (guard : d259614 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259612 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30541 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259613 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30546 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30548 (p : Pattern) (guard : d259615 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259614 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30547 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30549 (p : Pattern) (guard : d259616 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259615 p = 1 := by simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30548 p hg
    simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30550 (p : Pattern) (guard : d259617 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259616 p = 1 := by simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30549 p hg
    simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30551 (p : Pattern) (guard : d259679 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259678 p = 1 := by simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30545 p hg
    simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259617 p = 1 := by simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30550 p hg
    simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30552 (p : Pattern) (guard : d259680 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259679 p = 1 := by simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30551 p hg
    simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30553 (p : Pattern) (guard : d259681 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259680 p = 1 := by simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30552 p hg
    simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30554 (p : Pattern) (guard : d259706 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259681 p = 1 := by simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30553 p hg
    simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30555 (p : Pattern) (guard : d259618 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259613 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30546 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30556 (p : Pattern) (guard : d259619 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259618 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30555 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30557 (p : Pattern) (guard : d259620 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259619 p = 1 := by simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30556 p hg
    simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30558 (p : Pattern) (guard : d259621 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259620 p = 1 := by simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30557 p hg
    simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30559 (p : Pattern) (guard : d259622 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259617 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30550 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259621 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30558 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30560 (p : Pattern) (guard : d259623 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259622 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30559 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30561 (p : Pattern) (guard : d259624 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259623 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30560 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30562 (p : Pattern) (guard : d259638 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259624 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30561 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30563 (p : Pattern) (guard : d259707 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259706 p = 1 := by simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30554 p hg
    simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259638 p = 1 := by simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30562 p hg
    simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30564 (p : Pattern) (guard : d259708 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259707 p = 1 := by simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30563 p hg
    simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30565 (p : Pattern) (guard : d259685 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259617 p = 1 := by simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30550 p hg
    simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30566 (p : Pattern) (guard : d259686 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259685 p = 1 := by simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30565 p hg
    simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30567 (p : Pattern) (guard : d259687 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259686 p = 1 := by simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30566 p hg
    simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30568 (p : Pattern) (guard : d259709 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259687 p = 1 := by simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30567 p hg
    simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30569 (p : Pattern) (guard : d259710 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259709 p = 1 := by simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30568 p hg
    simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30570 (p : Pattern) (guard : d259711 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259710 p = 1 := by simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30569 p hg
    simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30571 (p : Pattern) (guard : d259712 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259708 p = 1 := by simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30564 p hg
    simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259711 p = 1 := by simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30570 p hg
    simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30572 (p : Pattern) (guard : d259733 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259712 p = 1 := by simpa only [d259733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30571 p hg
    simpa only [d259733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30573 (p : Pattern) (guard : d259734 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259733 p = 1 := by simpa only [d259734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30572 p hg
    simpa only [d259734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30574 (p : Pattern) (guard : d259735 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259735, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259735, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259734 p = 1 := by simpa only [d259735, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30573 p hg
    simpa only [d259735, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30575 (p : Pattern) (guard : d259736 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259735 p = 1 := by simpa only [d259736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30574 p hg
    simpa only [d259736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30576 (p : Pattern) (guard : d259626 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259621 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30558 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30577 (p : Pattern) (guard : d259627 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259626 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30576 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30578 (p : Pattern) (guard : d259628 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259627 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30577 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30579 (p : Pattern) (guard : d259639 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259628 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30578 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30580 (p : Pattern) (guard : d259723 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259639 p = 1 := by simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30579 p hg
    simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30581 (p : Pattern) (guard : d259724 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259723 p = 1 := by simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30580 p hg
    simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30582 (p : Pattern) (guard : d259725 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259724 p = 1 := by simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30581 p hg
    simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30583 (p : Pattern) (guard : d259726 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259725 p = 1 := by simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30582 p hg
    simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30584 (p : Pattern) (guard : d259727 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259726 p = 1 := by simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30583 p hg
    simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30585 (p : Pattern) (guard : d259737 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259727 p = 1 := by simpa only [d259737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30584 p hg
    simpa only [d259737, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30586 (p : Pattern) (guard : d259738 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259737 p = 1 := by simpa only [d259738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30585 p hg
    simpa only [d259738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30587 (p : Pattern) (guard : d259739 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259736 p = 1 := by simpa only [d259739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30575 p hg
    simpa only [d259739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259738 p = 1 := by simpa only [d259739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30586 p hg
    simpa only [d259739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30588 (p : Pattern) (guard : d259740 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259739 p = 1 := by simpa only [d259740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30587 p hg
    simpa only [d259740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30589 (p : Pattern) (guard : d259741 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259740 p = 1 := by simpa only [d259741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30588 p hg
    simpa only [d259741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30590 (p : Pattern) (guard : d259742 p = 1) : d47768 p ≤ (-1 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259732 p = 1 := by simpa only [d259742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30491 p hg
    simpa only [d259742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259741 p = 1 := by simpa only [d259742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30589 p hg
    simpa only [d259742, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30591 (p : Pattern) (guard : d258554 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d258554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258277 p = 1 := by simpa only [d258554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30178 p hg
    simpa only [d258554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30592 (p : Pattern) (guard : d259573 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29218 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30593 (p : Pattern) (guard : d259574 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30592 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30594 (p : Pattern) (guard : d259575 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29759 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30593 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30595 (p : Pattern) (guard : d259576 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29024 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30596 (p : Pattern) (guard : d259577 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30594 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30595 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30597 (p : Pattern) (guard : d259578 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30596 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30598 (p : Pattern) (guard : d259579 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30597 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30599 (p : Pattern) (guard : d259580 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30598 p hg
    simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30600 (p : Pattern) (guard : d259581 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30167 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30599 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30601 (p : Pattern) (guard : d259743 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259581 p = 1 := by simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30600 p hg
    simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30602 (p : Pattern) (guard : d259582 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30339 p hg
    simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30603 (p : Pattern) (guard : d259744 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259743 p = 1 := by simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30601 p hg
    simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259582 p = 1 := by simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30602 p hg
    simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30604 (p : Pattern) (guard : d259573 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29232 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30605 (p : Pattern) (guard : d259574 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30604 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30606 (p : Pattern) (guard : d259575 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29778 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30605 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30607 (p : Pattern) (guard : d259576 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29042 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30608 (p : Pattern) (guard : d259577 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30606 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30607 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30609 (p : Pattern) (guard : d259578 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30608 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30610 (p : Pattern) (guard : d259579 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30609 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30611 (p : Pattern) (guard : d259580 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30610 p hg
    simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30612 (p : Pattern) (guard : d259581 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30173 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30611 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30613 (p : Pattern) (guard : d259582 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30612 p hg
    simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30614 (p : Pattern) (guard : d259583 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259582 p = 1 := by simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30613 p hg
    simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30615 (p : Pattern) (guard : d259745 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259744 p = 1 := by simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30603 p hg
    simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259583 p = 1 := by simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30614 p hg
    simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30616 (p : Pattern) (guard : d259746 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259745 p = 1 := by simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30615 p hg
    simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30617 (p : Pattern) (guard : d259747 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258277 p = 1 := by simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30178 p hg
    simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259746 p = 1 := by simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30616 p hg
    simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30618 (p : Pattern) (guard : d259748 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258554 p = 1 := by simpa only [d259748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30591 p hg
    simpa only [d259748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259747 p = 1 := by simpa only [d259748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30617 p hg
    simpa only [d259748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30619 (p : Pattern) (guard : d259587 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30599 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30620 (p : Pattern) (guard : d259749 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259587 p = 1 := by simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30619 p hg
    simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30621 (p : Pattern) (guard : d259588 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30345 p hg
    simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30622 (p : Pattern) (guard : d259750 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259749 p = 1 := by simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30620 p hg
    simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259588 p = 1 := by simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30621 p hg
    simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30623 (p : Pattern) (guard : d259587 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30611 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29049 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30624 (p : Pattern) (guard : d259588 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30623 p hg
    simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30625 (p : Pattern) (guard : d259589 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259588 p = 1 := by simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30624 p hg
    simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30626 (p : Pattern) (guard : d259751 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259750 p = 1 := by simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30622 p hg
    simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259589 p = 1 := by simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30625 p hg
    simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30627 (p : Pattern) (guard : d259752 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259751 p = 1 := by simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30626 p hg
    simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30628 (p : Pattern) (guard : d259753 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259746 p = 1 := by simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30616 p hg
    simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259752 p = 1 := by simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30627 p hg
    simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30629 (p : Pattern) (guard : d259754 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259747 p = 1 := by simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30617 p hg
    simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259753 p = 1 := by simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30628 p hg
    simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30630 (p : Pattern) (guard : d259755 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259748 p = 1 := by simpa only [d259755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30618 p hg
    simpa only [d259755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259754 p = 1 := by simpa only [d259755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30629 p hg
    simpa only [d259755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30631 (p : Pattern) (guard : d259756 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259756, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259756, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259755 p = 1 := by simpa only [d259756, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30630 p hg
    simpa only [d259756, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30632 (p : Pattern) (guard : d259757 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259757, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259757, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259756 p = 1 := by simpa only [d259757, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30631 p hg
    simpa only [d259757, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30633 (p : Pattern) (guard : d259758 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259752 p = 1 := by simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30627 p hg
    simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30634 (p : Pattern) (guard : d259759 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259753 p = 1 := by simpa only [d259759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30628 p hg
    simpa only [d259759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259758 p = 1 := by simpa only [d259759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30633 p hg
    simpa only [d259759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30635 (p : Pattern) (guard : d259760 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259754 p = 1 := by simpa only [d259760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30629 p hg
    simpa only [d259760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259759 p = 1 := by simpa only [d259760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30634 p hg
    simpa only [d259760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30636 (p : Pattern) (guard : d259761 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259761, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259761, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259760 p = 1 := by simpa only [d259761, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30635 p hg
    simpa only [d259761, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30637 (p : Pattern) (guard : d259762 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259762, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259762, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259761 p = 1 := by simpa only [d259762, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30636 p hg
    simpa only [d259762, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30638 (p : Pattern) (guard : d259763 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259757 p = 1 := by simpa only [d259763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30632 p hg
    simpa only [d259763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259762 p = 1 := by simpa only [d259763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30637 p hg
    simpa only [d259763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30639 (p : Pattern) (guard : d259594 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30597 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30206 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30640 (p : Pattern) (guard : d259595 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30639 p hg
    simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30641 (p : Pattern) (guard : d259596 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30640 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30642 (p : Pattern) (guard : d259764 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259596 p = 1 := by simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30643 (p : Pattern) (guard : d259597 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30354 p hg
    simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30644 (p : Pattern) (guard : d259765 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259764 p = 1 := by simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30642 p hg
    simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259597 p = 1 := by simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30643 p hg
    simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30645 (p : Pattern) (guard : d259594 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30609 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30217 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30646 (p : Pattern) (guard : d259595 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30645 p hg
    simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30647 (p : Pattern) (guard : d259596 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30646 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29049 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30648 (p : Pattern) (guard : d259597 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30647 p hg
    simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30649 (p : Pattern) (guard : d259598 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259597 p = 1 := by simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30648 p hg
    simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30650 (p : Pattern) (guard : d259766 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259765 p = 1 := by simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30644 p hg
    simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259598 p = 1 := by simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30649 p hg
    simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30651 (p : Pattern) (guard : d259767 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259766 p = 1 := by simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30650 p hg
    simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30652 (p : Pattern) (guard : d259768 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259746 p = 1 := by simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30616 p hg
    simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259767 p = 1 := by simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30651 p hg
    simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30653 (p : Pattern) (guard : d259769 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259768 p = 1 := by simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30652 p hg
    simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259758 p = 1 := by simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30633 p hg
    simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30654 (p : Pattern) (guard : d259770 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259754 p = 1 := by simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30629 p hg
    simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259769 p = 1 := by simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30653 p hg
    simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30655 (p : Pattern) (guard : d259771 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259770 p = 1 := by simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30654 p hg
    simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30656 (p : Pattern) (guard : d259772 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259771 p = 1 := by simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30655 p hg
    simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30657 (p : Pattern) (guard : d259773 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259767 p = 1 := by simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30651 p hg
    simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30658 (p : Pattern) (guard : d259774 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259773 p = 1 := by simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30657 p hg
    simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30659 (p : Pattern) (guard : d259775 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259769 p = 1 := by simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30653 p hg
    simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259774 p = 1 := by simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30658 p hg
    simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30660 (p : Pattern) (guard : d259776 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259775 p = 1 := by simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30659 p hg
    simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30661 (p : Pattern) (guard : d259777 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259776 p = 1 := by simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30660 p hg
    simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30662 (p : Pattern) (guard : d259778 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259772 p = 1 := by simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30656 p hg
    simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259777 p = 1 := by simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30661 p hg
    simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30663 (p : Pattern) (guard : d259779 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259763 p = 1 := by simpa only [d259779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30638 p hg
    simpa only [d259779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259778 p = 1 := by simpa only [d259779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30662 p hg
    simpa only [d259779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30664 (p : Pattern) (guard : d259780 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259779 p = 1 := by simpa only [d259780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30663 p hg
    simpa only [d259780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30665 (p : Pattern) (guard : d259781 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259780 p = 1 := by simpa only [d259781, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30664 p hg
    simpa only [d259781, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259781, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259781, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30666 (p : Pattern) (guard : d259782 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259782, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259782, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259781 p = 1 := by simpa only [d259782, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30665 p hg
    simpa only [d259782, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30667 (p : Pattern) (guard : d259783 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259777 p = 1 := by simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30661 p hg
    simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30668 (p : Pattern) (guard : d259784 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259778 p = 1 := by simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30662 p hg
    simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259783 p = 1 := by simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30667 p hg
    simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30669 (p : Pattern) (guard : d259785 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259784 p = 1 := by simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30668 p hg
    simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30670 (p : Pattern) (guard : d259786 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259785 p = 1 := by simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30669 p hg
    simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30671 (p : Pattern) (guard : d259787 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259786 p = 1 := by simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30670 p hg
    simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30672 (p : Pattern) (guard : d259788 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259782 p = 1 := by simpa only [d259788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30666 p hg
    simpa only [d259788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259787 p = 1 := by simpa only [d259788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30671 p hg
    simpa only [d259788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30673 (p : Pattern) (guard : d259789 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259788 p = 1 := by simpa only [d259789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30672 p hg
    simpa only [d259789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30674 (p : Pattern) (guard : d259790 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259789 p = 1 := by simpa only [d259790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30673 p hg
    simpa only [d259790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30675 (p : Pattern) (guard : d259791 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259790 p = 1 := by simpa only [d259791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30674 p hg
    simpa only [d259791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30676 (p : Pattern) (guard : d259792 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259783 p = 1 := by simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30667 p hg
    simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30677 (p : Pattern) (guard : d259793 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259792 p = 1 := by simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30676 p hg
    simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30678 (p : Pattern) (guard : d259794 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259793 p = 1 := by simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30677 p hg
    simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30679 (p : Pattern) (guard : d259795 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259794 p = 1 := by simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30678 p hg
    simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30680 (p : Pattern) (guard : d259796 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259787 p = 1 := by simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30671 p hg
    simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259795 p = 1 := by simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30679 p hg
    simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30681 (p : Pattern) (guard : d259797 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259796 p = 1 := by simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30680 p hg
    simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30682 (p : Pattern) (guard : d259798 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259797 p = 1 := by simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30681 p hg
    simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30683 (p : Pattern) (guard : d259799 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259798 p = 1 := by simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30682 p hg
    simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30684 (p : Pattern) (guard : d259800 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259791 p = 1 := by simpa only [d259800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30675 p hg
    simpa only [d259800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259799 p = 1 := by simpa only [d259800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30683 p hg
    simpa only [d259800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30685 (p : Pattern) (guard : d259801 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259800 p = 1 := by simpa only [d259801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30684 p hg
    simpa only [d259801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30686 (p : Pattern) (guard : d259802 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259787 p = 1 := by simpa only [d259802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30671 p hg
    simpa only [d259802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30687 (p : Pattern) (guard : d259803 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259802 p = 1 := by simpa only [d259803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30686 p hg
    simpa only [d259803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30688 (p : Pattern) (guard : d259804 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259803 p = 1 := by simpa only [d259804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30687 p hg
    simpa only [d259804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30689 (p : Pattern) (guard : d259805 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259804 p = 1 := by simpa only [d259805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30688 p hg
    simpa only [d259805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30690 (p : Pattern) (guard : d259806 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259805 p = 1 := by simpa only [d259806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30689 p hg
    simpa only [d259806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30691 (p : Pattern) (guard : d259807 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259806 p = 1 := by simpa only [d259807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30690 p hg
    simpa only [d259807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30692 (p : Pattern) (guard : d259808 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259801 p = 1 := by simpa only [d259808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30685 p hg
    simpa only [d259808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259807 p = 1 := by simpa only [d259808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30691 p hg
    simpa only [d259808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30693 (p : Pattern) (guard : d259809 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259808 p = 1 := by simpa only [d259809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30692 p hg
    simpa only [d259809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30694 (p : Pattern) (guard : d259810 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259809 p = 1 := by simpa only [d259810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30693 p hg
    simpa only [d259810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30695 (p : Pattern) (guard : d259811 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259811, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259811, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259810 p = 1 := by simpa only [d259811, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30694 p hg
    simpa only [d259811, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30696 (p : Pattern) (guard : d259812 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259811 p = 1 := by simpa only [d259812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30695 p hg
    simpa only [d259812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30697 (p : Pattern) (guard : d259813 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259795 p = 1 := by simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30679 p hg
    simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30698 (p : Pattern) (guard : d259814 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259813 p = 1 := by simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30697 p hg
    simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30699 (p : Pattern) (guard : d259815 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259814 p = 1 := by simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30698 p hg
    simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30700 (p : Pattern) (guard : d259816 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259815 p = 1 := by simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30699 p hg
    simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30701 (p : Pattern) (guard : d259817 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259816 p = 1 := by simpa only [d259817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30700 p hg
    simpa only [d259817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30702 (p : Pattern) (guard : d259818 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259817 p = 1 := by simpa only [d259818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30701 p hg
    simpa only [d259818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30703 (p : Pattern) (guard : d259819 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259818 p = 1 := by simpa only [d259819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30702 p hg
    simpa only [d259819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30704 (p : Pattern) (guard : d259820 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259819 p = 1 := by simpa only [d259820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30703 p hg
    simpa only [d259820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30705 (p : Pattern) (guard : d259821 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259820 p = 1 := by simpa only [d259821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30704 p hg
    simpa only [d259821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30706 (p : Pattern) (guard : d259822 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259822, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259822, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259821 p = 1 := by simpa only [d259822, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30705 p hg
    simpa only [d259822, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30707 (p : Pattern) (guard : d259823 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259822 p = 1 := by simpa only [d259823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30706 p hg
    simpa only [d259823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30708 (p : Pattern) (guard : d259824 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259812 p = 1 := by simpa only [d259824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30696 p hg
    simpa only [d259824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259823 p = 1 := by simpa only [d259824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30707 p hg
    simpa only [d259824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30709 (p : Pattern) (guard : d259825 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259824 p = 1 := by simpa only [d259825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30708 p hg
    simpa only [d259825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30710 (p : Pattern) (guard : d259826 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259825 p = 1 := by simpa only [d259826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30709 p hg
    simpa only [d259826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30711 (p : Pattern) (guard : d259827 p = 1) : d47865 p ≤ (-1 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259826 p = 1 := by simpa only [d259827, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30710 p hg
    simpa only [d259827, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259827, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29083 p hg
    simpa only [d259827, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30712 (p : Pattern) (guard : d259828 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d259742 p = 1 := by simpa only [d259828, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30590 p hg
    simpa only [d259828, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259827 p = 1 := by simpa only [d259828, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30711 p hg
    simpa only [d259828, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30713 (p : Pattern) (guard : d259829 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259828 p = 1 := by simpa only [d259829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30712 p hg
    simpa only [d259829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30714 (p : Pattern) (guard : d259830 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259829 p = 1 := by simpa only [d259830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30713 p hg
    simpa only [d259830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30715 (p : Pattern) (guard : d259831 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259830 p = 1 := by simpa only [d259831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30714 p hg
    simpa only [d259831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30716 (p : Pattern) (guard : d259832 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259831 p = 1 := by simpa only [d259832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30715 p hg
    simpa only [d259832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30717 (p : Pattern) (guard : d259833 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259832 p = 1 := by simpa only [d259833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30716 p hg
    simpa only [d259833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30718 (p : Pattern) (guard : d259834 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259833 p = 1 := by simpa only [d259834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30717 p hg
    simpa only [d259834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30719 (p : Pattern) (guard : d259835 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259834 p = 1 := by simpa only [d259835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30718 p hg
    simpa only [d259835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30720 (p : Pattern) (guard : d259836 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259835 p = 1 := by simpa only [d259836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30719 p hg
    simpa only [d259836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30721 (p : Pattern) (guard : d259837 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259836 p = 1 := by simpa only [d259837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30720 p hg
    simpa only [d259837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30722 (p : Pattern) (guard : d259838 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259837 p = 1 := by simpa only [d259838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30721 p hg
    simpa only [d259838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30723 (p : Pattern) (guard : d259839 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d259572 p = 1 := by simpa only [d259839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30330 p hg
    simpa only [d259839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259838 p = 1 := by simpa only [d259839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30722 p hg
    simpa only [d259839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30724 (p : Pattern) (guard : d259840 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 260 with
  | false =>
    have hg : d259839 p = 1 := by simpa only [d259840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30723 p hg
    simpa only [d259840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30725 (p : Pattern) (guard : d259841 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 259 with
  | false =>
    have hg : d259840 p = 1 := by simpa only [d259841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30724 p hg
    simpa only [d259841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30726 (p : Pattern) (guard : d259842 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 258 with
  | false =>
    have hg : d259841 p = 1 := by simpa only [d259842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30725 p hg
    simpa only [d259842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30727 (p : Pattern) (guard : d259843 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 257 with
  | false =>
    have hg : d259842 p = 1 := by simpa only [d259843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30726 p hg
    simpa only [d259843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30728 (p : Pattern) (guard : d259844 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 256 with
  | false =>
    have hg : d259843 p = 1 := by simpa only [d259844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30727 p hg
    simpa only [d259844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30729 (p : Pattern) (guard : d259845 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 255 with
  | false =>
    have hg : d259844 p = 1 := by simpa only [d259845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30728 p hg
    simpa only [d259845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30730 (p : Pattern) (guard : d259846 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 254 with
  | false =>
    have hg : d259845 p = 1 := by simpa only [d259846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30729 p hg
    simpa only [d259846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30731 (p : Pattern) (guard : d259847 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 253 with
  | false =>
    have hg : d259846 p = 1 := by simpa only [d259847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30730 p hg
    simpa only [d259847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30732 (p : Pattern) (guard : d259848 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 252 with
  | false =>
    have hg : d259847 p = 1 := by simpa only [d259848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30731 p hg
    simpa only [d259848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30733 (p : Pattern) (guard : d259849 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 251 with
  | false =>
    have hg : d259848 p = 1 := by simpa only [d259849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30732 p hg
    simpa only [d259849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30734 (p : Pattern) (guard : d259850 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 250 with
  | false =>
    have hg : d259849 p = 1 := by simpa only [d259850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30733 p hg
    simpa only [d259850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30735 (p : Pattern) (guard : d259851 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 249 with
  | false =>
    have hg : d259850 p = 1 := by simpa only [d259851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30734 p hg
    simpa only [d259851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30736 (p : Pattern) (guard : d259852 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 245 with
  | false =>
    have hg : d259851 p = 1 := by simpa only [d259852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30735 p hg
    simpa only [d259852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30737 (p : Pattern) (guard : d259853 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 200 with
  | false =>
    have hg : d259852 p = 1 := by simpa only [d259853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30736 p hg
    simpa only [d259853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30738 (p : Pattern) (guard : d259854 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 199 with
  | false =>
    have hg : d259853 p = 1 := by simpa only [d259854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30737 p hg
    simpa only [d259854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30739 (p : Pattern) (guard : d259855 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 186 with
  | false =>
    have hg : d259854 p = 1 := by simpa only [d259855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30738 p hg
    simpa only [d259855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30740 (p : Pattern) (guard : d259856 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 185 with
  | false =>
    have hg : d259855 p = 1 := by simpa only [d259856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30739 p hg
    simpa only [d259856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30741 (p : Pattern) (guard : d259857 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 184 with
  | false =>
    have hg : d259856 p = 1 := by simpa only [d259857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30740 p hg
    simpa only [d259857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30742 (p : Pattern) (guard : d259858 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 181 with
  | false =>
    have hg : d259857 p = 1 := by simpa only [d259858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30741 p hg
    simpa only [d259858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30743 (p : Pattern) (guard : d259859 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 177 with
  | false =>
    have hg : d259858 p = 1 := by simpa only [d259859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30742 p hg
    simpa only [d259859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30744 (p : Pattern) (guard : d259860 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 164 with
  | false =>
    have hg : d259859 p = 1 := by simpa only [d259860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30743 p hg
    simpa only [d259860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30745 (p : Pattern) (guard : d259861 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 156 with
  | false =>
    have hg : d259860 p = 1 := by simpa only [d259861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30744 p hg
    simpa only [d259861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30746 (p : Pattern) (guard : d259862 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 155 with
  | false =>
    have hg : d259861 p = 1 := by simpa only [d259862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30745 p hg
    simpa only [d259862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30747 (p : Pattern) (guard : d259863 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 134 with
  | false =>
    have hg : d259862 p = 1 := by simpa only [d259863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30746 p hg
    simpa only [d259863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30748 (p : Pattern) (guard : d259864 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 133 with
  | false =>
    have hg : d259863 p = 1 := by simpa only [d259864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30747 p hg
    simpa only [d259864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30749 (p : Pattern) (guard : d259865 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 120 with
  | false =>
    have hg : d259864 p = 1 := by simpa only [d259865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30748 p hg
    simpa only [d259865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259865, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
