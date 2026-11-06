import NetHack.Soko22Hazard87.Bounds000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare0 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d48083 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (0 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d48080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (0 : Int) + d47865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d47865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16 (p : Pattern) (guard : d59964 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare17 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18 (p : Pattern) (guard : d0 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19 (p : Pattern) (guard : d0 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21 (p : Pattern) (guard : d0 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (0 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23 (p : Pattern) (guard : d0 p = 1) : d47786 p ≤ (0 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24 (p : Pattern) (guard : d0 p = 1) : d47796 p ≤ (0 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (0 : Int) + d47704 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare27 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (0 : Int) + d47714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26 p hg
    simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d15, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30 (p : Pattern) (guard : d16 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31 (p : Pattern) (guard : d17 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32 (p : Pattern) (guard : d18 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33 (p : Pattern) (guard : d19 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34 (p : Pattern) (guard : d20 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35 (p : Pattern) (guard : d21 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36 (p : Pattern) (guard : d22 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37 (p : Pattern) (guard : d0 p = 1) : d47631 p ≤ (0 : Int) + d47716 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38 (p : Pattern) (guard : d23 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36 p hg
    simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d23, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40 (p : Pattern) (guard : d24 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41 (p : Pattern) (guard : d66 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d24 p = 1 := by simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40 p hg
    simpa only [d66, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare43 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (0 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42 p hg
    simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43 p hg
    simpa only [d15, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46 (p : Pattern) (guard : d16 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47 (p : Pattern) (guard : d17 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48 (p : Pattern) (guard : d18 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49 (p : Pattern) (guard : d19 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare50 (p : Pattern) (guard : d20 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare51 (p : Pattern) (guard : d21 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare52 (p : Pattern) (guard : d22 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare51 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare53 (p : Pattern) (guard : d0 p = 1) : d47618 p ≤ (0 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare54 (p : Pattern) (guard : d23 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare52 p hg
    simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d23, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare55 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare56 (p : Pattern) (guard : d24 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare54 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare57 (p : Pattern) (guard : d0 p = 1) : d47661 p ≤ (0 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare58 (p : Pattern) (guard : d25 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare56 p hg
    simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d25, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare59 (p : Pattern) (guard : d67 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d66 p = 1 := by simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41 p hg
    simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25 p = 1 := by simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare58 p hg
    simpa only [d67, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare60 (p : Pattern) (guard : d0 p = 1) : d47683 p ≤ (0 : Int) + d47736 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare61 (p : Pattern) (guard : d17561 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d67 p = 1 := by simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare59 p hg
    simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17561, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare62 (p : Pattern) (guard : d0 p = 1) : d47802 p ≤ (0 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare63 (p : Pattern) (guard : d17562 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17561 p = 1 := by simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare61 p hg
    simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17562, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare64 (p : Pattern) (guard : d0 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare65 (p : Pattern) (guard : d17563 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17562 p = 1 := by simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare63 p hg
    simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d17563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare66 (p : Pattern) (guard : d17564 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17563 p = 1 := by simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d17564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare67 (p : Pattern) (guard : d17565 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17564 p = 1 := by simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare66 p hg
    simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d17565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare68 (p : Pattern) (guard : d17566 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17565 p = 1 := by simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d17566, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare69 (p : Pattern) (guard : d17567 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17566 p = 1 := by simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare68 p hg
    simpa only [d17567, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare70 (p : Pattern) (guard : d0 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare71 (p : Pattern) (guard : d17568 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17567 p = 1 := by simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare72 (p : Pattern) (guard : d17569 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17568 p = 1 := by simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare73 (p : Pattern) (guard : d17570 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17569 p = 1 := by simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare72 p hg
    simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare74 (p : Pattern) (guard : d0 p = 1) : d47806 p ≤ (0 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare75 (p : Pattern) (guard : d17571 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17570 p = 1 := by simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare73 p hg
    simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d17571, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare76 (p : Pattern) (guard : d17572 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17571 p = 1 := by simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d17572, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare77 (p : Pattern) (guard : d17573 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17572 p = 1 := by simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare76 p hg
    simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare78 (p : Pattern) (guard : d17574 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17573 p = 1 := by simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare79 (p : Pattern) (guard : d17575 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17574 p = 1 := by simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare80 (p : Pattern) (guard : d17576 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17575 p = 1 := by simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare79 p hg
    simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare81 (p : Pattern) (guard : d17577 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17576 p = 1 := by simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare80 p hg
    simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare82 (p : Pattern) (guard : d17578 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17577 p = 1 := by simpa only [d17578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare81 p hg
    simpa only [d17578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare83 (p : Pattern) (guard : d17579 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17578 p = 1 := by simpa only [d17579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare82 p hg
    simpa only [d17579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare84 (p : Pattern) (guard : d17580 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17579 p = 1 := by simpa only [d17580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare83 p hg
    simpa only [d17580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare85 (p : Pattern) (guard : d17581 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17580 p = 1 := by simpa only [d17581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d17581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare86 (p : Pattern) (guard : d17582 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17582, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d17582, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17581 p = 1 := by simpa only [d17582, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare85 p hg
    simpa only [d17582, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare87 (p : Pattern) (guard : d17583 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d17583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17582 p = 1 := by simpa only [d17583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare86 p hg
    simpa only [d17583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare88 (p : Pattern) (guard : d17584 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17583 p = 1 := by simpa only [d17584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare87 p hg
    simpa only [d17584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d17584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare89 (p : Pattern) (guard : d17585 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d17584 p = 1 := by simpa only [d17585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d17585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d17585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare90 (p : Pattern) (guard : d17586 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d17585 p = 1 := by simpa only [d17586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare89 p hg
    simpa only [d17586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d17586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare91 (p : Pattern) (guard : d0 p = 1) : d47864 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare92 (p : Pattern) (guard : d17587 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d17586 p = 1 := by simpa only [d17587, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare90 p hg
    simpa only [d17587, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17587, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d17587, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare93 (p : Pattern) (guard : d17588 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17588, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d17588, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17587 p = 1 := by simpa only [d17588, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare92 p hg
    simpa only [d17588, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare94 (p : Pattern) (guard : d17589 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d17589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17588 p = 1 := by simpa only [d17589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare93 p hg
    simpa only [d17589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare95 (p : Pattern) (guard : d17590 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d17590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17589 p = 1 := by simpa only [d17590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare94 p hg
    simpa only [d17590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare96 (p : Pattern) (guard : d17591 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d17591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17590 p = 1 := by simpa only [d17591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare95 p hg
    simpa only [d17591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare97 (p : Pattern) (guard : d17592 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d17592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17591 p = 1 := by simpa only [d17592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare96 p hg
    simpa only [d17592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare98 (p : Pattern) (guard : d128 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare99 (p : Pattern) (guard : d13 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare100 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare101 (p : Pattern) (guard : d14 p = 1) : d47629 p ≤ (0 : Int) + d47714 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare99 p hg
    simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d14, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare102 (p : Pattern) (guard : d129 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare101 p hg
    simpa only [d129, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare103 (p : Pattern) (guard : d130 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare102 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare104 (p : Pattern) (guard : d131 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare105 (p : Pattern) (guard : d132 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare104 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare106 (p : Pattern) (guard : d133 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare105 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare107 (p : Pattern) (guard : d134 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare106 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare108 (p : Pattern) (guard : d135 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare107 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare109 (p : Pattern) (guard : d136 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare110 (p : Pattern) (guard : d137 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d137, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare111 (p : Pattern) (guard : d138 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare112 (p : Pattern) (guard : d226 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d138 p = 1 := by simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare111 p hg
    simpa only [d226, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare113 (p : Pattern) (guard : d128 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare114 (p : Pattern) (guard : d13 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare115 (p : Pattern) (guard : d14 p = 1) : d47616 p ≤ (0 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare114 p hg
    simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d14, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare116 (p : Pattern) (guard : d129 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare113 p hg
    simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d129, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare117 (p : Pattern) (guard : d130 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44 p hg
    simpa only [d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare118 (p : Pattern) (guard : d131 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d130 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46 p hg
    simpa only [d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare119 (p : Pattern) (guard : d132 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare118 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47 p hg
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare120 (p : Pattern) (guard : d133 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare119 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare121 (p : Pattern) (guard : d134 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d133 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare120 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare122 (p : Pattern) (guard : d135 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare121 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare50 p hg
    simpa only [d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare123 (p : Pattern) (guard : d136 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d135 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare51 p hg
    simpa only [d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare124 (p : Pattern) (guard : d137 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d136 p = 1 := by simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d137, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare125 (p : Pattern) (guard : d138 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d23 p = 1 := by simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare54 p hg
    simpa only [d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare126 (p : Pattern) (guard : d139 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d138 p = 1 := by simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare125 p hg
    simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d139, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare127 (p : Pattern) (guard : d227 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d226 p = 1 := by simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare112 p hg
    simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d139 p = 1 := by simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare126 p hg
    simpa only [d227, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare128 (p : Pattern) (guard : d17593 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d227 p = 1 := by simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare127 p hg
    simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17593, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare129 (p : Pattern) (guard : d17594 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17593 p = 1 := by simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare128 p hg
    simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17594, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare130 (p : Pattern) (guard : d17595 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17594 p = 1 := by simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17562 p = 1 := by simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare63 p hg
    simpa only [d17595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare131 (p : Pattern) (guard : d17596 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17595 p = 1 := by simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare130 p hg
    simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17563 p = 1 := by simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d17596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare132 (p : Pattern) (guard : d17597 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17596 p = 1 := by simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare131 p hg
    simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17564 p = 1 := by simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare66 p hg
    simpa only [d17597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare133 (p : Pattern) (guard : d17598 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17597 p = 1 := by simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare132 p hg
    simpa only [d17598, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare134 (p : Pattern) (guard : d17599 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17598 p = 1 := by simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare133 p hg
    simpa only [d17599, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare135 (p : Pattern) (guard : d17600 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17599 p = 1 := by simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17567 p = 1 := by simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d17600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare136 (p : Pattern) (guard : d17601 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17600 p = 1 := by simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare135 p hg
    simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17568 p = 1 := by simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d17601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare137 (p : Pattern) (guard : d17602 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17601 p = 1 := by simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare136 p hg
    simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d17602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare138 (p : Pattern) (guard : d17603 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17602 p = 1 := by simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare137 p hg
    simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d17603, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare139 (p : Pattern) (guard : d17604 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17603 p = 1 := by simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare138 p hg
    simpa only [d17604, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare140 (p : Pattern) (guard : d17605 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17604 p = 1 := by simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare139 p hg
    simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17572 p = 1 := by simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare76 p hg
    simpa only [d17605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare141 (p : Pattern) (guard : d17606 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17605 p = 1 := by simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare140 p hg
    simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare142 (p : Pattern) (guard : d17607 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17606 p = 1 := by simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare141 p hg
    simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare143 (p : Pattern) (guard : d17608 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17607 p = 1 := by simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare142 p hg
    simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare144 (p : Pattern) (guard : d17609 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17608 p = 1 := by simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare143 p hg
    simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17576 p = 1 := by simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare80 p hg
    simpa only [d17609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare145 (p : Pattern) (guard : d60559 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17609 p = 1 := by simpa only [d60559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare144 p hg
    simpa only [d60559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare146 (p : Pattern) (guard : d60560 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60559 p = 1 := by simpa only [d60560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare145 p hg
    simpa only [d60560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17578 p = 1 := by simpa only [d60560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare82 p hg
    simpa only [d60560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare147 (p : Pattern) (guard : d60561 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60560 p = 1 := by simpa only [d60561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare146 p hg
    simpa only [d60561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare148 (p : Pattern) (guard : d60562 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60561 p = 1 := by simpa only [d60562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare147 p hg
    simpa only [d60562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare149 (p : Pattern) (guard : d60563 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60563, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60563, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60562 p = 1 := by simpa only [d60563, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare148 p hg
    simpa only [d60563, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare150 (p : Pattern) (guard : d60564 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60563 p = 1 := by simpa only [d60564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare149 p hg
    simpa only [d60564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare151 (p : Pattern) (guard : d60565 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d60564 p = 1 := by simpa only [d60565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare150 p hg
    simpa only [d60565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare152 (p : Pattern) (guard : d60566 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d60565 p = 1 := by simpa only [d60566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare151 p hg
    simpa only [d60566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare153 (p : Pattern) (guard : d60567 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d60566 p = 1 := by simpa only [d60567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare152 p hg
    simpa only [d60567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare154 (p : Pattern) (guard : d60568 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d60567 p = 1 := by simpa only [d60568, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare153 p hg
    simpa only [d60568, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60568, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d60568, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare155 (p : Pattern) (guard : d60569 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60569, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d60569, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60568 p = 1 := by simpa only [d60569, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare154 p hg
    simpa only [d60569, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare156 (p : Pattern) (guard : d60570 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60569 p = 1 := by simpa only [d60570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare155 p hg
    simpa only [d60570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare157 (p : Pattern) (guard : d60571 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60570 p = 1 := by simpa only [d60571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare156 p hg
    simpa only [d60571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare158 (p : Pattern) (guard : d60572 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60571 p = 1 := by simpa only [d60572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare157 p hg
    simpa only [d60572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare159 (p : Pattern) (guard : d60573 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60572 p = 1 := by simpa only [d60573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare158 p hg
    simpa only [d60573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare160 (p : Pattern) (guard : d60574 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d17592 p = 1 := by simpa only [d60574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d60574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60573 p = 1 := by simpa only [d60574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare159 p hg
    simpa only [d60574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare161 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare162 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  have ha := bounds2 p
  have hb := bounds3 p
  omega
theorem compare163 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (0 : Int) + d47714 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare162 p hg
    simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d308, d47629, d47714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare164 (p : Pattern) (guard : d309 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare161 p hg
    simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d309, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare165 (p : Pattern) (guard : d310 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare102 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare166 (p : Pattern) (guard : d311 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare165 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare167 (p : Pattern) (guard : d312 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare166 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare104 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare168 (p : Pattern) (guard : d313 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare167 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare169 (p : Pattern) (guard : d314 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare168 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare170 (p : Pattern) (guard : d315 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare169 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare107 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare171 (p : Pattern) (guard : d316 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare170 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare172 (p : Pattern) (guard : d317 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare171 p hg
    simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d317, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare173 (p : Pattern) (guard : d318 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare172 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare110 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare174 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318 p = 1 := by simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare173 p hg
    simpa only [d412, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare175 (p : Pattern) (guard : d307 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare176 (p : Pattern) (guard : d127 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  have ha := bounds4 p
  have hb := bounds5 p
  omega
theorem compare177 (p : Pattern) (guard : d308 p = 1) : d47616 p ≤ (0 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare176 p hg
    simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d308, d47616, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare178 (p : Pattern) (guard : d309 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare175 p hg
    simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare177 p hg
    simpa only [d309, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare179 (p : Pattern) (guard : d310 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare178 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare116 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare180 (p : Pattern) (guard : d311 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare179 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare117 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare181 (p : Pattern) (guard : d312 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare180 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare118 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare182 (p : Pattern) (guard : d313 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare181 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare183 (p : Pattern) (guard : d314 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare182 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare184 (p : Pattern) (guard : d315 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare183 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare121 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare185 (p : Pattern) (guard : d316 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare184 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare122 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare186 (p : Pattern) (guard : d317 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare185 p hg
    simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d317, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare187 (p : Pattern) (guard : d318 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare124 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare188 (p : Pattern) (guard : d319 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare187 p hg
    simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d319, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare189 (p : Pattern) (guard : d413 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare174 p hg
    simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d319 p = 1 := by simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare188 p hg
    simpa only [d413, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare190 (p : Pattern) (guard : d17643 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d413 p = 1 := by simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d17643, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare191 (p : Pattern) (guard : d17644 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17643 p = 1 := by simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare190 p hg
    simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d17644, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare192 (p : Pattern) (guard : d17645 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d17644 p = 1 := by simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17594 p = 1 := by simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare129 p hg
    simpa only [d17645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare193 (p : Pattern) (guard : d60575 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17645 p = 1 := by simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare192 p hg
    simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17595 p = 1 := by simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare130 p hg
    simpa only [d60575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare194 (p : Pattern) (guard : d60576 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60575 p = 1 := by simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare193 p hg
    simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17596 p = 1 := by simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare131 p hg
    simpa only [d60576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare195 (p : Pattern) (guard : d60577 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60576 p = 1 := by simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare194 p hg
    simpa only [d60577, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare196 (p : Pattern) (guard : d60578 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60577 p = 1 := by simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare195 p hg
    simpa only [d60578, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare197 (p : Pattern) (guard : d60579 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60578 p = 1 := by simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare196 p hg
    simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17599 p = 1 := by simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d60579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare198 (p : Pattern) (guard : d60580 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60579 p = 1 := by simpa only [d60580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare197 p hg
    simpa only [d60580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17600 p = 1 := by simpa only [d60580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare135 p hg
    simpa only [d60580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare199 (p : Pattern) (guard : d60581 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60580 p = 1 := by simpa only [d60581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare198 p hg
    simpa only [d60581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare200 (p : Pattern) (guard : d60582 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60581 p = 1 := by simpa only [d60582, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d60582, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60582, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60582, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare201 (p : Pattern) (guard : d60583 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60583, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60583, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60582 p = 1 := by simpa only [d60583, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d60583, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare202 (p : Pattern) (guard : d60584 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60583 p = 1 := by simpa only [d60584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d60584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17604 p = 1 := by simpa only [d60584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare139 p hg
    simpa only [d60584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare203 (p : Pattern) (guard : d60585 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60584 p = 1 := by simpa only [d60585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare202 p hg
    simpa only [d60585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare204 (p : Pattern) (guard : d60586 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60585 p = 1 := by simpa only [d60586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d60586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare205 (p : Pattern) (guard : d60587 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60586 p = 1 := by simpa only [d60587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare204 p hg
    simpa only [d60587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare206 (p : Pattern) (guard : d60588 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60587 p = 1 := by simpa only [d60588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare205 p hg
    simpa only [d60588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17608 p = 1 := by simpa only [d60588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare143 p hg
    simpa only [d60588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare207 (p : Pattern) (guard : d60589 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60588 p = 1 := by simpa only [d60589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare206 p hg
    simpa only [d60589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare208 (p : Pattern) (guard : d60590 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17608 p = 1 := by simpa only [d60590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare143 p hg
    simpa only [d60590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare209 (p : Pattern) (guard : d60591 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60590 p = 1 := by simpa only [d60591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d60591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare210 (p : Pattern) (guard : d60592 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60589 p = 1 := by simpa only [d60592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare207 p hg
    simpa only [d60592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60591 p = 1 := by simpa only [d60592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d60592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare211 (p : Pattern) (guard : d60593 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60592 p = 1 := by simpa only [d60593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare210 p hg
    simpa only [d60593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare212 (p : Pattern) (guard : d60594 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60593 p = 1 := by simpa only [d60594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d60594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare213 (p : Pattern) (guard : d60595 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60595, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60595, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60594 p = 1 := by simpa only [d60595, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare212 p hg
    simpa only [d60595, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare214 (p : Pattern) (guard : d60596 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60595 p = 1 := by simpa only [d60596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare213 p hg
    simpa only [d60596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare215 (p : Pattern) (guard : d17692 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17577 p = 1 := by simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare81 p hg
    simpa only [d17692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare216 (p : Pattern) (guard : d17693 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17692 p = 1 := by simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare217 (p : Pattern) (guard : d17694 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17693 p = 1 := by simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare216 p hg
    simpa only [d17694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare218 (p : Pattern) (guard : d17695 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17694 p = 1 := by simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d17695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare219 (p : Pattern) (guard : d17696 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17695 p = 1 := by simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d17696, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare220 (p : Pattern) (guard : d17697 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17696 p = 1 := by simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare219 p hg
    simpa only [d17697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare221 (p : Pattern) (guard : d60597 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d60596 p = 1 := by simpa only [d60597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare214 p hg
    simpa only [d60597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17697 p = 1 := by simpa only [d60597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare220 p hg
    simpa only [d60597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare222 (p : Pattern) (guard : d60598 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d60597 p = 1 := by simpa only [d60598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d60598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare223 (p : Pattern) (guard : d60599 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d60598 p = 1 := by simpa only [d60599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d60599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare224 (p : Pattern) (guard : d60600 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d60599 p = 1 := by simpa only [d60600, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d60600, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60600, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d60600, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare225 (p : Pattern) (guard : d60601 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60601, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d60601, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60600 p = 1 := by simpa only [d60601, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare224 p hg
    simpa only [d60601, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare226 (p : Pattern) (guard : d60602 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60601 p = 1 := by simpa only [d60602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d60602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare227 (p : Pattern) (guard : d60603 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60602 p = 1 := by simpa only [d60603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare226 p hg
    simpa only [d60603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare228 (p : Pattern) (guard : d60604 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60603 p = 1 := by simpa only [d60604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare227 p hg
    simpa only [d60604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare229 (p : Pattern) (guard : d60605 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60604 p = 1 := by simpa only [d60605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d60605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare230 (p : Pattern) (guard : d60606 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60605 p = 1 := by simpa only [d60606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d60606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare231 (p : Pattern) (guard : d60607 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d60574 p = 1 := by simpa only [d60607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare160 p hg
    simpa only [d60607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60606 p = 1 := by simpa only [d60607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare230 p hg
    simpa only [d60607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare232 (p : Pattern) (guard : d528 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare233 (p : Pattern) (guard : d529 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare165 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare234 (p : Pattern) (guard : d530 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare233 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare166 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare235 (p : Pattern) (guard : d531 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare236 (p : Pattern) (guard : d532 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare235 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare237 (p : Pattern) (guard : d533 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare169 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare238 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare102 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare239 (p : Pattern) (guard : d535 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare165 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare238 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare240 (p : Pattern) (guard : d536 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare239 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare104 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare241 (p : Pattern) (guard : d537 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare240 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare242 (p : Pattern) (guard : d538 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare241 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare243 (p : Pattern) (guard : d539 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare107 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare244 (p : Pattern) (guard : d540 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare243 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare245 (p : Pattern) (guard : d541 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare244 p hg
    simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d541, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare246 (p : Pattern) (guard : d542 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare245 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare172 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare247 (p : Pattern) (guard : d659 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d542 p = 1 := by simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare246 p hg
    simpa only [d659, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare248 (p : Pattern) (guard : d528 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare178 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare249 (p : Pattern) (guard : d529 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare248 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare179 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
