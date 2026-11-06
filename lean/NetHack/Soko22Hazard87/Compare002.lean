import NetHack.Soko22Hazard87.Compare001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare500 (p : Pattern) (guard : d1100 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare499 p hg
    simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1100, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare501 (p : Pattern) (guard : d1381 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1380 p = 1 := by simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare492 p hg
    simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1100 p = 1 := by simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d1381, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare502 (p : Pattern) (guard : d17953 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1381 p = 1 := by simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare501 p hg
    simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17953, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare503 (p : Pattern) (guard : d17954 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17953 p = 1 := by simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare502 p hg
    simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17954, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare504 (p : Pattern) (guard : d60700 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17943 p = 1 := by simpa only [d60700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare484 p hg
    simpa only [d60700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17954 p = 1 := by simpa only [d60700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare503 p hg
    simpa only [d60700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare505 (p : Pattern) (guard : d1104 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare105 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare506 (p : Pattern) (guard : d1105 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare505 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare507 (p : Pattern) (guard : d1106 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare487 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare506 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare508 (p : Pattern) (guard : d1107 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare507 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare509 (p : Pattern) (guard : d1108 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare508 p hg
    simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1108, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare510 (p : Pattern) (guard : d1109 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare509 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare511 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1109 p = 1 := by simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare510 p hg
    simpa only [d1385, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare512 (p : Pattern) (guard : d1104 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare119 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare513 (p : Pattern) (guard : d1105 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare512 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare514 (p : Pattern) (guard : d1106 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare495 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare513 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare515 (p : Pattern) (guard : d1107 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare514 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare516 (p : Pattern) (guard : d1108 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare515 p hg
    simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1108, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare517 (p : Pattern) (guard : d1109 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare498 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare516 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare518 (p : Pattern) (guard : d1110 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare517 p hg
    simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1110, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare519 (p : Pattern) (guard : d1386 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1110 p = 1 := by simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare518 p hg
    simpa only [d1386, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare520 (p : Pattern) (guard : d17974 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1386 p = 1 := by simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17974, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare521 (p : Pattern) (guard : d17975 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17974 p = 1 := by simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare520 p hg
    simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17975, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare522 (p : Pattern) (guard : d60701 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17954 p = 1 := by simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare503 p hg
    simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17975 p = 1 := by simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d60701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare523 (p : Pattern) (guard : d60702 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60700 p = 1 := by simpa only [d60702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare504 p hg
    simpa only [d60702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60701 p = 1 := by simpa only [d60702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare522 p hg
    simpa only [d60702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare524 (p : Pattern) (guard : d1115 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare525 (p : Pattern) (guard : d1116 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare524 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare526 (p : Pattern) (guard : d1117 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare525 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare527 (p : Pattern) (guard : d1118 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare526 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare528 (p : Pattern) (guard : d1119 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare527 p hg
    simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1119, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare529 (p : Pattern) (guard : d1120 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare509 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare528 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare530 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1120 p = 1 := by simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare529 p hg
    simpa only [d1391, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare531 (p : Pattern) (guard : d1115 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare532 (p : Pattern) (guard : d1116 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare531 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare533 (p : Pattern) (guard : d1117 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare532 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare534 (p : Pattern) (guard : d1118 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare533 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare51 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare535 (p : Pattern) (guard : d1119 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare534 p hg
    simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1119, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare536 (p : Pattern) (guard : d1120 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare516 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare535 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare537 (p : Pattern) (guard : d1121 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1121, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare538 (p : Pattern) (guard : d1392 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare530 p hg
    simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1121 p = 1 := by simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare537 p hg
    simpa only [d1392, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare539 (p : Pattern) (guard : d17976 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1392 p = 1 := by simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare538 p hg
    simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17976, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare540 (p : Pattern) (guard : d17977 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17976 p = 1 := by simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17977, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare541 (p : Pattern) (guard : d17978 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17975 p = 1 := by simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17977 p = 1 := by simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare540 p hg
    simpa only [d17978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare542 (p : Pattern) (guard : d60703 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60701 p = 1 := by simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare522 p hg
    simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17978 p = 1 := by simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare541 p hg
    simpa only [d60703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare543 (p : Pattern) (guard : d60704 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60702 p = 1 := by simpa only [d60704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d60704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60703 p = 1 := by simpa only [d60704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d60704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare544 (p : Pattern) (guard : d60705 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60705, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60705, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60704 p = 1 := by simpa only [d60705, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare543 p hg
    simpa only [d60705, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare545 (p : Pattern) (guard : d60706 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60706, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60706, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60705 p = 1 := by simpa only [d60706, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare544 p hg
    simpa only [d60706, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare546 (p : Pattern) (guard : d18007 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17977 p = 1 := by simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare540 p hg
    simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d18007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare547 (p : Pattern) (guard : d60707 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17978 p = 1 := by simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare541 p hg
    simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18007 p = 1 := by simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare546 p hg
    simpa only [d60707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare548 (p : Pattern) (guard : d60708 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60703 p = 1 := by simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60707 p = 1 := by simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare547 p hg
    simpa only [d60708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare549 (p : Pattern) (guard : d60709 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60708 p = 1 := by simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare548 p hg
    simpa only [d60709, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare550 (p : Pattern) (guard : d60710 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60709 p = 1 := by simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare549 p hg
    simpa only [d60710, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare551 (p : Pattern) (guard : d60711 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60706 p = 1 := by simpa only [d60711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare545 p hg
    simpa only [d60711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60710 p = 1 := by simpa only [d60711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare550 p hg
    simpa only [d60711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare552 (p : Pattern) (guard : d1132 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare525 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare553 (p : Pattern) (guard : d1133 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare552 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare554 (p : Pattern) (guard : d1134 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare553 p hg
    simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1134, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare555 (p : Pattern) (guard : d1135 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare554 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare556 (p : Pattern) (guard : d1406 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1135 p = 1 := by simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare555 p hg
    simpa only [d1406, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare557 (p : Pattern) (guard : d1132 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare532 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare558 (p : Pattern) (guard : d1133 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare557 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare559 (p : Pattern) (guard : d1134 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare558 p hg
    simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1134, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare560 (p : Pattern) (guard : d1135 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare561 (p : Pattern) (guard : d1136 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare560 p hg
    simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1136, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare562 (p : Pattern) (guard : d1407 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1406 p = 1 := by simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare556 p hg
    simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1136 p = 1 := by simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare561 p hg
    simpa only [d1407, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare563 (p : Pattern) (guard : d60712 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1407 p = 1 := by simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare562 p hg
    simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d60712, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare564 (p : Pattern) (guard : d60713 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d60712 p = 1 := by simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d60713, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare565 (p : Pattern) (guard : d60714 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d60713 p = 1 := by simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare564 p hg
    simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d60714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare566 (p : Pattern) (guard : d60715 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d18007 p = 1 := by simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare546 p hg
    simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60714 p = 1 := by simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare565 p hg
    simpa only [d60715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare567 (p : Pattern) (guard : d60716 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60707 p = 1 := by simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare547 p hg
    simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60715 p = 1 := by simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare566 p hg
    simpa only [d60716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare568 (p : Pattern) (guard : d60717 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60716 p = 1 := by simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare567 p hg
    simpa only [d60717, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare569 (p : Pattern) (guard : d60718 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60717 p = 1 := by simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare568 p hg
    simpa only [d60718, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare570 (p : Pattern) (guard : d60719 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60710 p = 1 := by simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare550 p hg
    simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60718 p = 1 := by simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare569 p hg
    simpa only [d60719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare571 (p : Pattern) (guard : d60720 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60711 p = 1 := by simpa only [d60720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare551 p hg
    simpa only [d60720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60719 p = 1 := by simpa only [d60720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare570 p hg
    simpa only [d60720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare572 (p : Pattern) (guard : d60721 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60720 p = 1 := by simpa only [d60721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare571 p hg
    simpa only [d60721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare573 (p : Pattern) (guard : d60722 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60721 p = 1 := by simpa only [d60722, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare572 p hg
    simpa only [d60722, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60722, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60722, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare574 (p : Pattern) (guard : d60723 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60723, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60723, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60722 p = 1 := by simpa only [d60723, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare573 p hg
    simpa only [d60723, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare575 (p : Pattern) (guard : d60724 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60718 p = 1 := by simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare569 p hg
    simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare576 (p : Pattern) (guard : d60725 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60719 p = 1 := by simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare570 p hg
    simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60724 p = 1 := by simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d60725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare577 (p : Pattern) (guard : d60726 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60725 p = 1 := by simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare576 p hg
    simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare578 (p : Pattern) (guard : d60727 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60726 p = 1 := by simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare577 p hg
    simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60727, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare579 (p : Pattern) (guard : d60728 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60727 p = 1 := by simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare578 p hg
    simpa only [d60728, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare580 (p : Pattern) (guard : d60729 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60723 p = 1 := by simpa only [d60729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare574 p hg
    simpa only [d60729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60728 p = 1 := by simpa only [d60729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare579 p hg
    simpa only [d60729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare581 (p : Pattern) (guard : d60730 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60729 p = 1 := by simpa only [d60730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare580 p hg
    simpa only [d60730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare582 (p : Pattern) (guard : d60731 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60730 p = 1 := by simpa only [d60731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare581 p hg
    simpa only [d60731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare583 (p : Pattern) (guard : d60732 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60731 p = 1 := by simpa only [d60732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare582 p hg
    simpa only [d60732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare584 (p : Pattern) (guard : d60733 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60724 p = 1 := by simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare585 (p : Pattern) (guard : d60734 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60733 p = 1 := by simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare584 p hg
    simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare586 (p : Pattern) (guard : d60735 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60734 p = 1 := by simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare585 p hg
    simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60735, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare587 (p : Pattern) (guard : d60736 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60735 p = 1 := by simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare586 p hg
    simpa only [d60736, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare588 (p : Pattern) (guard : d60737 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60728 p = 1 := by simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare579 p hg
    simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60736 p = 1 := by simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare587 p hg
    simpa only [d60737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare589 (p : Pattern) (guard : d60738 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60737 p = 1 := by simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare588 p hg
    simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare590 (p : Pattern) (guard : d60739 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60738 p = 1 := by simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare589 p hg
    simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare591 (p : Pattern) (guard : d60740 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60739 p = 1 := by simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare590 p hg
    simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare592 (p : Pattern) (guard : d60741 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60732 p = 1 := by simpa only [d60741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare583 p hg
    simpa only [d60741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60740 p = 1 := by simpa only [d60741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare591 p hg
    simpa only [d60741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare593 (p : Pattern) (guard : d60742 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60741 p = 1 := by simpa only [d60742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare592 p hg
    simpa only [d60742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare594 (p : Pattern) (guard : d60743 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60740 p = 1 := by simpa only [d60743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare591 p hg
    simpa only [d60743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare595 (p : Pattern) (guard : d60744 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60743 p = 1 := by simpa only [d60744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare594 p hg
    simpa only [d60744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare596 (p : Pattern) (guard : d60745 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60742 p = 1 := by simpa only [d60745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare593 p hg
    simpa only [d60745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60744 p = 1 := by simpa only [d60745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare595 p hg
    simpa only [d60745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare597 (p : Pattern) (guard : d60746 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60745 p = 1 := by simpa only [d60746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare596 p hg
    simpa only [d60746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare598 (p : Pattern) (guard : d60747 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60746 p = 1 := by simpa only [d60747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare597 p hg
    simpa only [d60747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare599 (p : Pattern) (guard : d60748 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60748, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60748, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60747 p = 1 := by simpa only [d60748, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare598 p hg
    simpa only [d60748, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare600 (p : Pattern) (guard : d60749 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60748 p = 1 := by simpa only [d60749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare599 p hg
    simpa only [d60749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare601 (p : Pattern) (guard : d60750 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60736 p = 1 := by simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare587 p hg
    simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare602 (p : Pattern) (guard : d60751 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60750 p = 1 := by simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare601 p hg
    simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare603 (p : Pattern) (guard : d60752 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60751 p = 1 := by simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare602 p hg
    simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare604 (p : Pattern) (guard : d60753 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60752 p = 1 := by simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare603 p hg
    simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare605 (p : Pattern) (guard : d60754 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60753 p = 1 := by simpa only [d60754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare604 p hg
    simpa only [d60754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare606 (p : Pattern) (guard : d60755 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60754 p = 1 := by simpa only [d60755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare605 p hg
    simpa only [d60755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare607 (p : Pattern) (guard : d60756 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60755 p = 1 := by simpa only [d60756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare606 p hg
    simpa only [d60756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare608 (p : Pattern) (guard : d60757 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60756 p = 1 := by simpa only [d60757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare607 p hg
    simpa only [d60757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare609 (p : Pattern) (guard : d60758 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60757 p = 1 := by simpa only [d60758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare608 p hg
    simpa only [d60758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare610 (p : Pattern) (guard : d60759 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60759, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60759, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60758 p = 1 := by simpa only [d60759, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare609 p hg
    simpa only [d60759, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare611 (p : Pattern) (guard : d60760 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60759 p = 1 := by simpa only [d60760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare610 p hg
    simpa only [d60760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare612 (p : Pattern) (guard : d60761 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d60749 p = 1 := by simpa only [d60761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare600 p hg
    simpa only [d60761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60760 p = 1 := by simpa only [d60761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare611 p hg
    simpa only [d60761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare613 (p : Pattern) (guard : d60762 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d60761 p = 1 := by simpa only [d60762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare612 p hg
    simpa only [d60762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare614 (p : Pattern) (guard : d60763 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d60762 p = 1 := by simpa only [d60763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d60763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare615 (p : Pattern) (guard : d60764 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d60763 p = 1 := by simpa only [d60764, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare614 p hg
    simpa only [d60764, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60764, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d60764, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare616 (p : Pattern) (guard : d60765 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60765, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d60765, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60764 p = 1 := by simpa only [d60765, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare615 p hg
    simpa only [d60765, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare617 (p : Pattern) (guard : d60766 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60765 p = 1 := by simpa only [d60766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare616 p hg
    simpa only [d60766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare618 (p : Pattern) (guard : d60767 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60766 p = 1 := by simpa only [d60767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare617 p hg
    simpa only [d60767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare619 (p : Pattern) (guard : d60768 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60767 p = 1 := by simpa only [d60768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare618 p hg
    simpa only [d60768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare620 (p : Pattern) (guard : d60769 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60768 p = 1 := by simpa only [d60769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare619 p hg
    simpa only [d60769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare621 (p : Pattern) (guard : d60770 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60769 p = 1 := by simpa only [d60770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare620 p hg
    simpa only [d60770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare622 (p : Pattern) (guard : d60771 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60770 p = 1 := by simpa only [d60771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare621 p hg
    simpa only [d60771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare623 (p : Pattern) (guard : d60772 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60771 p = 1 := by simpa only [d60772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare622 p hg
    simpa only [d60772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare624 (p : Pattern) (guard : d60773 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60772 p = 1 := by simpa only [d60773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare623 p hg
    simpa only [d60773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare625 (p : Pattern) (guard : d60774 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d60699 p = 1 := by simpa only [d60774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare437 p hg
    simpa only [d60774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60773 p = 1 := by simpa only [d60774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare624 p hg
    simpa only [d60774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare626 (p : Pattern) (guard : d1660 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1201 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare627 (p : Pattern) (guard : d1661 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1205 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare628 (p : Pattern) (guard : d1662 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1660 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare626 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1661 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare627 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare629 (p : Pattern) (guard : d1663 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1662 p = 1 := by simpa only [d1663, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare628 p hg
    simpa only [d1663, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1663, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1663, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare630 (p : Pattern) (guard : d308 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare631 (p : Pattern) (guard : d1519 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare630 p hg
    simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d1519, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare632 (p : Pattern) (guard : d1520 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare633 (p : Pattern) (guard : d1521 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare632 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare634 (p : Pattern) (guard : d1522 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare633 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare635 (p : Pattern) (guard : d1523 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare448 p hg
    simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d1523, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare636 (p : Pattern) (guard : d1524 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare637 (p : Pattern) (guard : d1525 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare638 (p : Pattern) (guard : d1526 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare637 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare639 (p : Pattern) (guard : d1527 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare634 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare638 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare640 (p : Pattern) (guard : d1528 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare641 (p : Pattern) (guard : d1529 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare639 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare640 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare642 (p : Pattern) (guard : d1530 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare641 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare643 (p : Pattern) (guard : d1531 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare644 (p : Pattern) (guard : d1532 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare632 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare643 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare645 (p : Pattern) (guard : d1533 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare644 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare646 (p : Pattern) (guard : d1534 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare645 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare647 (p : Pattern) (guard : d1535 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare646 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare648 (p : Pattern) (guard : d1536 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare444 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare649 (p : Pattern) (guard : d1537 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare642 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare648 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare650 (p : Pattern) (guard : d1538 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare649 p hg
    simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1538, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare651 (p : Pattern) (guard : d1664 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1663 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare629 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1538 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare650 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare652 (p : Pattern) (guard : d1853 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1853, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1853, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1664 p = 1 := by simpa only [d1853, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare651 p hg
    simpa only [d1853, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare653 (p : Pattern) (guard : d1660 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1201 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare462 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare654 (p : Pattern) (guard : d1661 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1205 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare466 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare655 (p : Pattern) (guard : d1662 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1660 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare653 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1661 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare654 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare656 (p : Pattern) (guard : d1663 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1662 p = 1 := by simpa only [d1663, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare655 p hg
    simpa only [d1663, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1663, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1663, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare657 (p : Pattern) (guard : d308 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare658 (p : Pattern) (guard : d1519 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare657 p hg
    simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43 p hg
    simpa only [d1519, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare659 (p : Pattern) (guard : d1520 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare178 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare658 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare660 (p : Pattern) (guard : d1521 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare248 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare661 (p : Pattern) (guard : d1522 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare662 (p : Pattern) (guard : d1523 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare470 p hg
    simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare177 p hg
    simpa only [d1523, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare663 (p : Pattern) (guard : d1524 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare662 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare471 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare664 (p : Pattern) (guard : d1525 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare663 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare665 (p : Pattern) (guard : d1526 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare666 (p : Pattern) (guard : d1527 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare667 (p : Pattern) (guard : d1528 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare668 (p : Pattern) (guard : d1529 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare666 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare667 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare669 (p : Pattern) (guard : d1530 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare462 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare668 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare670 (p : Pattern) (guard : d1531 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare658 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare671 (p : Pattern) (guard : d1532 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare670 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare672 (p : Pattern) (guard : d1533 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare671 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare673 (p : Pattern) (guard : d1534 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare672 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare674 (p : Pattern) (guard : d1535 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare673 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare675 (p : Pattern) (guard : d1536 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare466 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare674 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare676 (p : Pattern) (guard : d1537 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare669 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare675 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare677 (p : Pattern) (guard : d1538 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare676 p hg
    simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1538, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare678 (p : Pattern) (guard : d1664 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1663 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare656 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1538 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare679 (p : Pattern) (guard : d1665 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d1665, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1665, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare680 (p : Pattern) (guard : d1854 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1853 p = 1 := by simpa only [d1854, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare652 p hg
    simpa only [d1854, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1665 p = 1 := by simpa only [d1854, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare679 p hg
    simpa only [d1854, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare681 (p : Pattern) (guard : d18123 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1854 p = 1 := by simpa only [d18123, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d18123, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18123, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18123, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare682 (p : Pattern) (guard : d18124 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18123 p = 1 := by simpa only [d18124, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare681 p hg
    simpa only [d18124, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18124, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18124, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare683 (p : Pattern) (guard : d1539 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare633 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare644 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare684 (p : Pattern) (guard : d1540 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare685 (p : Pattern) (guard : d1541 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare686 (p : Pattern) (guard : d1542 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare637 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare687 (p : Pattern) (guard : d1543 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare683 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare688 (p : Pattern) (guard : d1544 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare485 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare689 (p : Pattern) (guard : d1545 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare690 (p : Pattern) (guard : d1546 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare641 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare691 (p : Pattern) (guard : d1547 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare643 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare692 (p : Pattern) (guard : d1548 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare644 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare693 (p : Pattern) (guard : d1549 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare694 (p : Pattern) (guard : d1550 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare695 (p : Pattern) (guard : d1551 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare696 (p : Pattern) (guard : d1552 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare695 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare697 (p : Pattern) (guard : d1553 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare696 p hg
    simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1553, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare698 (p : Pattern) (guard : d1554 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare650 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare699 (p : Pattern) (guard : d1857 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1554 p = 1 := by simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d1857, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare700 (p : Pattern) (guard : d1539 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare671 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare701 (p : Pattern) (guard : d1540 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare658 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare702 (p : Pattern) (guard : d1541 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare701 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare703 (p : Pattern) (guard : d1542 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare702 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare704 (p : Pattern) (guard : d1543 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare703 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare705 (p : Pattern) (guard : d1544 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare493 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare706 (p : Pattern) (guard : d1545 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare704 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare705 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare707 (p : Pattern) (guard : d1546 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare668 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare708 (p : Pattern) (guard : d1547 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare670 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare709 (p : Pattern) (guard : d1548 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare671 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare708 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare710 (p : Pattern) (guard : d1549 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare711 (p : Pattern) (guard : d1550 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare712 (p : Pattern) (guard : d1551 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare674 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare713 (p : Pattern) (guard : d1552 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare714 (p : Pattern) (guard : d1553 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare713 p hg
    simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1553, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare715 (p : Pattern) (guard : d1554 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare716 (p : Pattern) (guard : d1555 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1555, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare717 (p : Pattern) (guard : d1858 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1857 p = 1 := by simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1555 p = 1 := by simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare716 p hg
    simpa only [d1858, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare718 (p : Pattern) (guard : d18134 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1858 p = 1 := by simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare717 p hg
    simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18134, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare719 (p : Pattern) (guard : d18135 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18134 p = 1 := by simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare718 p hg
    simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18135, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare720 (p : Pattern) (guard : d60775 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18124 p = 1 := by simpa only [d60775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d60775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18135 p = 1 := by simpa only [d60775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare719 p hg
    simpa only [d60775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare721 (p : Pattern) (guard : d1559 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare722 (p : Pattern) (guard : d1560 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare721 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare723 (p : Pattern) (guard : d1561 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare722 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare524 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare724 (p : Pattern) (guard : d1562 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare723 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare725 (p : Pattern) (guard : d1563 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare726 (p : Pattern) (guard : d1564 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare725 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare727 (p : Pattern) (guard : d1565 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare726 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare728 (p : Pattern) (guard : d1566 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare729 (p : Pattern) (guard : d1567 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare724 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare730 (p : Pattern) (guard : d1568 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare729 p hg
    simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1568, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare731 (p : Pattern) (guard : d1569 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare732 (p : Pattern) (guard : d1862 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1569 p = 1 := by simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare731 p hg
    simpa only [d1862, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare733 (p : Pattern) (guard : d1559 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare702 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare734 (p : Pattern) (guard : d1560 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare733 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare735 (p : Pattern) (guard : d1561 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare531 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare736 (p : Pattern) (guard : d1562 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare737 (p : Pattern) (guard : d1563 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare708 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare738 (p : Pattern) (guard : d1564 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare737 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare739 (p : Pattern) (guard : d1565 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare738 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare740 (p : Pattern) (guard : d1566 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare739 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare741 (p : Pattern) (guard : d1567 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare736 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare740 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare742 (p : Pattern) (guard : d1568 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare741 p hg
    simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1568, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare743 (p : Pattern) (guard : d1569 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare742 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare744 (p : Pattern) (guard : d1570 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare743 p hg
    simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1570, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare745 (p : Pattern) (guard : d1863 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1862 p = 1 := by simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1570 p = 1 := by simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare744 p hg
    simpa only [d1863, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare746 (p : Pattern) (guard : d18155 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1863 p = 1 := by simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18155, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare747 (p : Pattern) (guard : d18156 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18155 p = 1 := by simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare746 p hg
    simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18156, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare748 (p : Pattern) (guard : d60776 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18135 p = 1 := by simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare719 p hg
    simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18156 p = 1 := by simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare747 p hg
    simpa only [d60776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare749 (p : Pattern) (guard : d60777 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60775 p = 1 := by simpa only [d60777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare720 p hg
    simpa only [d60777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60776 p = 1 := by simpa only [d60777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare748 p hg
    simpa only [d60777, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
