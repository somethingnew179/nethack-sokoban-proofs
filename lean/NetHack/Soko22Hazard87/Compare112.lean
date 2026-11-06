import NetHack.Soko22Hazard87.Compare111
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28000 (p : Pattern) (guard : d16439 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27999 p hg
    simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d16439, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28001 (p : Pattern) (guard : d16440 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27983 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28000 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28002 (p : Pattern) (guard : d9581 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27989 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28003 (p : Pattern) (guard : d9582 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9581 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28002 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28004 (p : Pattern) (guard : d9768 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27963 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28003 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28005 (p : Pattern) (guard : d9769 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9768 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28004 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28006 (p : Pattern) (guard : d9770 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9769 p = 1 := by simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28005 p hg
    simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d9770, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28007 (p : Pattern) (guard : d9777 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9770 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28006 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27995 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28008 (p : Pattern) (guard : d9778 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28007 p hg
    simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d9778, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28009 (p : Pattern) (guard : d9780 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28008 p hg
    simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d9780, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28010 (p : Pattern) (guard : d14758 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28009 p hg
    simpa only [d14758, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28011 (p : Pattern) (guard : d14759 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28010 p hg
    simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d14759, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28012 (p : Pattern) (guard : d9795 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27975 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27751 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28013 (p : Pattern) (guard : d9796 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27527 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28014 (p : Pattern) (guard : d9797 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28012 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28013 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28015 (p : Pattern) (guard : d9798 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28014 p hg
    simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d9798, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28016 (p : Pattern) (guard : d1115 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27446 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28017 (p : Pattern) (guard : d1116 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28016 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28018 (p : Pattern) (guard : d1117 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28017 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27448 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28019 (p : Pattern) (guard : d1118 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28018 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27449 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28020 (p : Pattern) (guard : d1119 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28019 p hg
    simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1119, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28021 (p : Pattern) (guard : d9799 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28015 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28020 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28022 (p : Pattern) (guard : d9800 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28021 p hg
    simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d9800, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28023 (p : Pattern) (guard : d9802 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28022 p hg
    simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d9802, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28024 (p : Pattern) (guard : d14763 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28023 p hg
    simpa only [d14763, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28025 (p : Pattern) (guard : d14764 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28024 p hg
    simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d14764, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28026 (p : Pattern) (guard : d16441 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28011 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28025 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28027 (p : Pattern) (guard : d16442 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28001 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28026 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28028 (p : Pattern) (guard : d1104 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27525 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27446 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28029 (p : Pattern) (guard : d1105 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28028 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28030 (p : Pattern) (guard : d1106 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27975 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28029 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28031 (p : Pattern) (guard : d1107 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28030 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27528 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28032 (p : Pattern) (guard : d1108 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28031 p hg
    simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1108, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28033 (p : Pattern) (guard : d1109 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27978 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28032 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28034 (p : Pattern) (guard : d1110 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28033 p hg
    simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d1110, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28035 (p : Pattern) (guard : d1111 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28034 p hg
    simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d1111, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28036 (p : Pattern) (guard : d1112 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28035 p hg
    simpa only [d1112, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28037 (p : Pattern) (guard : d1113 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28036 p hg
    simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d1113, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28038 (p : Pattern) (guard : d1120 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28032 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28020 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28039 (p : Pattern) (guard : d1121 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28038 p hg
    simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d1121, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28040 (p : Pattern) (guard : d1122 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28039 p hg
    simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d1122, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28041 (p : Pattern) (guard : d1123 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28040 p hg
    simpa only [d1123, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28042 (p : Pattern) (guard : d1124 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28041 p hg
    simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d1124, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28043 (p : Pattern) (guard : d1125 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28037 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28042 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28044 (p : Pattern) (guard : d14765 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28025 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28045 (p : Pattern) (guard : d16443 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28043 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28044 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28046 (p : Pattern) (guard : d16444 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28027 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28045 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28047 (p : Pattern) (guard : d19061 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16444 p = 1 := by simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28046 p hg
    simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19061, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28048 (p : Pattern) (guard : d19062 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19061 p = 1 := by simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28047 p hg
    simpa only [d19062, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28049 (p : Pattern) (guard : d5012 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27749 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27446 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28050 (p : Pattern) (guard : d5013 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28049 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28051 (p : Pattern) (guard : d5014 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27975 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28050 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28052 (p : Pattern) (guard : d5015 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28051 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27528 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28053 (p : Pattern) (guard : d5016 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28052 p hg
    simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d5016, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28054 (p : Pattern) (guard : d5017 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28053 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28020 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28055 (p : Pattern) (guard : d5018 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28054 p hg
    simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d5018, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28056 (p : Pattern) (guard : d5019 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28055 p hg
    simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d5019, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28057 (p : Pattern) (guard : d5020 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28056 p hg
    simpa only [d5020, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28058 (p : Pattern) (guard : d5021 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28057 p hg
    simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d5021, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28059 (p : Pattern) (guard : d5022 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28058 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28060 (p : Pattern) (guard : d1132 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28017 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28061 (p : Pattern) (guard : d9841 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28060 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27449 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28062 (p : Pattern) (guard : d9842 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9841 p = 1 := by simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28061 p hg
    simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d9842, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28063 (p : Pattern) (guard : d9843 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9842 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28062 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28064 (p : Pattern) (guard : d9844 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28063 p hg
    simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d9844, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28065 (p : Pattern) (guard : d9846 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28064 p hg
    simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d9846, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28066 (p : Pattern) (guard : d14770 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28065 p hg
    simpa only [d14770, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28067 (p : Pattern) (guard : d14771 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28066 p hg
    simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d14771, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28068 (p : Pattern) (guard : d14772 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28067 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28069 (p : Pattern) (guard : d14773 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28059 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28068 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28070 (p : Pattern) (guard : d16447 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28045 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28069 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28071 (p : Pattern) (guard : d19063 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16447 p = 1 := by simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28070 p hg
    simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19063, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28072 (p : Pattern) (guard : d19064 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19063 p = 1 := by simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28071 p hg
    simpa only [d19064, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28073 (p : Pattern) (guard : d19065 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19062 p = 1 := by simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28048 p hg
    simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19064 p = 1 := by simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28072 p hg
    simpa only [d19065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28074 (p : Pattern) (guard : d1127 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28042 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28075 (p : Pattern) (guard : d14778 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28074 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28068 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28076 (p : Pattern) (guard : d16451 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28045 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28075 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28077 (p : Pattern) (guard : d19088 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16451 p = 1 := by simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28076 p hg
    simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19088, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28078 (p : Pattern) (guard : d19089 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19088 p = 1 := by simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28077 p hg
    simpa only [d19089, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28079 (p : Pattern) (guard : d19090 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19089 p = 1 := by simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28078 p hg
    simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d19090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28080 (p : Pattern) (guard : d132455 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19065 p = 1 := by simpa only [d132455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28073 p hg
    simpa only [d132455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19090 p = 1 := by simpa only [d132455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28079 p hg
    simpa only [d132455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28081 (p : Pattern) (guard : d188356 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d188356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27952 p hg
    simpa only [d188356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d132455 p = 1 := by simpa only [d188356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28080 p hg
    simpa only [d188356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28082 (p : Pattern) (guard : d188357 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188356 p = 1 := by simpa only [d188357, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28081 p hg
    simpa only [d188357, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188357, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188357, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28083 (p : Pattern) (guard : d188358 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188358, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188358, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188357 p = 1 := by simpa only [d188358, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28082 p hg
    simpa only [d188358, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28084 (p : Pattern) (guard : d16459 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27951 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28085 (p : Pattern) (guard : d19091 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19090 p = 1 := by simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28079 p hg
    simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d19091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28086 (p : Pattern) (guard : d188080 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28084 p hg
    simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19091 p = 1 := by simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28085 p hg
    simpa only [d188080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28087 (p : Pattern) (guard : d188081 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188080 p = 1 := by simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28086 p hg
    simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188081, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28088 (p : Pattern) (guard : d188082 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188081 p = 1 := by simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28087 p hg
    simpa only [d188082, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28089 (p : Pattern) (guard : d188359 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188358 p = 1 := by simpa only [d188359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28083 p hg
    simpa only [d188359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188082 p = 1 := by simpa only [d188359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28088 p hg
    simpa only [d188359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28090 (p : Pattern) (guard : d188360 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188359 p = 1 := by simpa only [d188360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28089 p hg
    simpa only [d188360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28091 (p : Pattern) (guard : d188361 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188360 p = 1 := by simpa only [d188361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28090 p hg
    simpa only [d188361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28092 (p : Pattern) (guard : d188362 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188361 p = 1 := by simpa only [d188362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28091 p hg
    simpa only [d188362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28093 (p : Pattern) (guard : d188103 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188082 p = 1 := by simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28088 p hg
    simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28094 (p : Pattern) (guard : d188104 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188103 p = 1 := by simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28093 p hg
    simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28095 (p : Pattern) (guard : d188105 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188104 p = 1 := by simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28094 p hg
    simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28096 (p : Pattern) (guard : d188106 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188105 p = 1 := by simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28095 p hg
    simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28097 (p : Pattern) (guard : d188363 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188362 p = 1 := by simpa only [d188363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28092 p hg
    simpa only [d188363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188106 p = 1 := by simpa only [d188363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28096 p hg
    simpa only [d188363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28098 (p : Pattern) (guard : d188364 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188363 p = 1 := by simpa only [d188364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28097 p hg
    simpa only [d188364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28099 (p : Pattern) (guard : d188365 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188364 p = 1 := by simpa only [d188365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28098 p hg
    simpa only [d188365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28100 (p : Pattern) (guard : d188366 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188365 p = 1 := by simpa only [d188366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28099 p hg
    simpa only [d188366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28101 (p : Pattern) (guard : d188367 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188366 p = 1 := by simpa only [d188367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28100 p hg
    simpa only [d188367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28102 (p : Pattern) (guard : d188368 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188368, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d188368, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188367 p = 1 := by simpa only [d188368, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28101 p hg
    simpa only [d188368, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28103 (p : Pattern) (guard : d188369 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188368 p = 1 := by simpa only [d188369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28102 p hg
    simpa only [d188369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28104 (p : Pattern) (guard : d188370 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188369 p = 1 := by simpa only [d188370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28103 p hg
    simpa only [d188370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28105 (p : Pattern) (guard : d188371 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188370 p = 1 := by simpa only [d188371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28104 p hg
    simpa only [d188371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28106 (p : Pattern) (guard : d188372 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188371 p = 1 := by simpa only [d188372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28105 p hg
    simpa only [d188372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28107 (p : Pattern) (guard : d188373 p = 1) : d48748 p ≤ (-2 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188372 p = 1 := by simpa only [d188373, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28106 p hg
    simpa only [d188373, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188373, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d188373, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28108 (p : Pattern) (guard : d188374 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188374, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d188374, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188373 p = 1 := by simpa only [d188374, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28107 p hg
    simpa only [d188374, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28109 (p : Pattern) (guard : d188375 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188374 p = 1 := by simpa only [d188375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28108 p hg
    simpa only [d188375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28110 (p : Pattern) (guard : d188376 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188375 p = 1 := by simpa only [d188376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28109 p hg
    simpa only [d188376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28111 (p : Pattern) (guard : d188377 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188376 p = 1 := by simpa only [d188377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28110 p hg
    simpa only [d188377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28112 (p : Pattern) (guard : d188378 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188377 p = 1 := by simpa only [d188378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28111 p hg
    simpa only [d188378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28113 (p : Pattern) (guard : d188379 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188378 p = 1 := by simpa only [d188379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28112 p hg
    simpa only [d188379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28114 (p : Pattern) (guard : d188380 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188379 p = 1 := by simpa only [d188380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28113 p hg
    simpa only [d188380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28115 (p : Pattern) (guard : d188381 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188380 p = 1 := by simpa only [d188381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28114 p hg
    simpa only [d188381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28116 (p : Pattern) (guard : d188382 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188381 p = 1 := by simpa only [d188382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28115 p hg
    simpa only [d188382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28117 (p : Pattern) (guard : d188383 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d188355 p = 1 := by simpa only [d188383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27824 p hg
    simpa only [d188383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188382 p = 1 := by simpa only [d188383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28116 p hg
    simpa only [d188383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28118 (p : Pattern) (guard : d1199 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27825 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28119 (p : Pattern) (guard : d1200 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28118 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28120 (p : Pattern) (guard : d1201 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28119 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28121 (p : Pattern) (guard : d1520 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27571 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27858 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28122 (p : Pattern) (guard : d1521 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27669 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28121 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28123 (p : Pattern) (guard : d1522 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27825 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28122 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28124 (p : Pattern) (guard : d1523 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27829 p hg
    simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27570 p hg
    simpa only [d1523, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28125 (p : Pattern) (guard : d1524 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28124 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27830 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28126 (p : Pattern) (guard : d1525 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28125 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28127 (p : Pattern) (guard : d1526 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28126 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28128 (p : Pattern) (guard : d1527 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28123 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28127 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28129 (p : Pattern) (guard : d1528 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27833 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28130 (p : Pattern) (guard : d1529 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28128 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28129 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28131 (p : Pattern) (guard : d1530 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28120 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28130 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28132 (p : Pattern) (guard : d1203 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27838 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28133 (p : Pattern) (guard : d1204 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28132 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28134 (p : Pattern) (guard : d1205 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28133 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28135 (p : Pattern) (guard : d1532 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28121 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27859 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28136 (p : Pattern) (guard : d1533 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27838 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28135 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28137 (p : Pattern) (guard : d1534 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28136 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28138 (p : Pattern) (guard : d1535 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28137 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28139 (p : Pattern) (guard : d1536 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28134 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28138 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28140 (p : Pattern) (guard : d1537 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28131 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28139 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28141 (p : Pattern) (guard : d1538 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28140 p hg
    simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28142 (p : Pattern) (guard : d1539 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28122 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28135 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28143 (p : Pattern) (guard : d1540 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27858 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27410 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28144 (p : Pattern) (guard : d1541 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28143 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28145 (p : Pattern) (guard : d1542 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28126 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28144 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28146 (p : Pattern) (guard : d1543 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28142 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28145 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28147 (p : Pattern) (guard : d1544 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27845 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28148 (p : Pattern) (guard : d1545 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28146 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28147 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28149 (p : Pattern) (guard : d1546 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28130 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28148 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28150 (p : Pattern) (guard : d1547 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27859 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28151 (p : Pattern) (guard : d1548 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28135 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28150 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28152 (p : Pattern) (guard : d1549 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28151 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28153 (p : Pattern) (guard : d1550 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28152 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28154 (p : Pattern) (guard : d1551 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28138 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28153 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28155 (p : Pattern) (guard : d1552 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28149 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28154 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28156 (p : Pattern) (guard : d1553 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28155 p hg
    simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28157 (p : Pattern) (guard : d1554 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28141 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28156 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28158 (p : Pattern) (guard : d1555 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28157 p hg
    simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28159 (p : Pattern) (guard : d1556 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28158 p hg
    simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28160 (p : Pattern) (guard : d1557 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28159 p hg
    simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28161 (p : Pattern) (guard : d1558 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28160 p hg
    simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28162 (p : Pattern) (guard : d2005 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28124 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28163 (p : Pattern) (guard : d2006 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28162 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28164 (p : Pattern) (guard : d10054 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28163 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28165 (p : Pattern) (guard : d10055 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28164 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28166 (p : Pattern) (guard : d10056 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10055 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28165 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28167 (p : Pattern) (guard : d5122 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27856 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28150 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28168 (p : Pattern) (guard : d10057 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28167 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28169 (p : Pattern) (guard : d10058 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28168 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28170 (p : Pattern) (guard : d10059 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10056 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28166 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28169 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28171 (p : Pattern) (guard : d10060 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10059 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28170 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28172 (p : Pattern) (guard : d10061 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10060 p = 1 := by simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28171 p hg
    simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28173 (p : Pattern) (guard : d10073 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28156 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28172 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28174 (p : Pattern) (guard : d10074 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28173 p hg
    simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28175 (p : Pattern) (guard : d10076 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28174 p hg
    simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28176 (p : Pattern) (guard : d16787 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28175 p hg
    simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28177 (p : Pattern) (guard : d16788 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28176 p hg
    simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28178 (p : Pattern) (guard : d16789 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28161 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28177 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28179 (p : Pattern) (guard : d10051 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28130 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28180 (p : Pattern) (guard : d10052 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10051 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28179 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28181 (p : Pattern) (guard : d10053 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10052 p = 1 := by simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28180 p hg
    simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28182 (p : Pattern) (guard : d10062 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10053 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28181 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28172 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28183 (p : Pattern) (guard : d10063 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28182 p hg
    simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28184 (p : Pattern) (guard : d10065 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28183 p hg
    simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28185 (p : Pattern) (guard : d15151 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28184 p hg
    simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28186 (p : Pattern) (guard : d15152 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28185 p hg
    simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28187 (p : Pattern) (guard : d10080 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28148 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28169 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28188 (p : Pattern) (guard : d10081 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28153 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28189 (p : Pattern) (guard : d10082 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28187 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28188 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28190 (p : Pattern) (guard : d10083 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28189 p hg
    simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28191 (p : Pattern) (guard : d1563 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28150 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28192 (p : Pattern) (guard : d5128 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28191 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28193 (p : Pattern) (guard : d5129 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5128 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28192 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28194 (p : Pattern) (guard : d1564 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28191 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28195 (p : Pattern) (guard : d1565 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28194 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28196 (p : Pattern) (guard : d5130 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5129 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28193 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28195 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28197 (p : Pattern) (guard : d1578 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28195 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28198 (p : Pattern) (guard : d5131 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5130 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28196 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28197 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28199 (p : Pattern) (guard : d5132 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5131 p = 1 := by simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28198 p hg
    simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28200 (p : Pattern) (guard : d10084 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28190 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28199 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28201 (p : Pattern) (guard : d10085 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28200 p hg
    simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28202 (p : Pattern) (guard : d10087 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28201 p hg
    simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28203 (p : Pattern) (guard : d15156 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28202 p hg
    simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28204 (p : Pattern) (guard : d15157 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28203 p hg
    simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28205 (p : Pattern) (guard : d16790 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28186 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28204 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28206 (p : Pattern) (guard : d16791 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28178 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28205 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28207 (p : Pattern) (guard : d1559 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28144 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28208 (p : Pattern) (guard : d1560 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28151 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28207 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28209 (p : Pattern) (guard : d1561 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28208 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27888 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28210 (p : Pattern) (guard : d1562 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28148 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28209 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28211 (p : Pattern) (guard : d1566 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28153 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28195 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28212 (p : Pattern) (guard : d1567 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28210 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28211 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28213 (p : Pattern) (guard : d1568 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28212 p hg
    simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28214 (p : Pattern) (guard : d1569 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28156 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28213 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28215 (p : Pattern) (guard : d1570 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28214 p hg
    simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28216 (p : Pattern) (guard : d1571 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28215 p hg
    simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28217 (p : Pattern) (guard : d1572 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28216 p hg
    simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28218 (p : Pattern) (guard : d1573 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28217 p hg
    simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28219 (p : Pattern) (guard : d10114 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28213 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28199 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28220 (p : Pattern) (guard : d10115 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28219 p hg
    simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28221 (p : Pattern) (guard : d10117 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28220 p hg
    simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28222 (p : Pattern) (guard : d16792 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28221 p hg
    simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28223 (p : Pattern) (guard : d16793 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28222 p hg
    simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28224 (p : Pattern) (guard : d16794 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28218 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28223 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28225 (p : Pattern) (guard : d15158 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28204 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28226 (p : Pattern) (guard : d16795 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28224 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28225 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28227 (p : Pattern) (guard : d16796 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28206 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28226 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28228 (p : Pattern) (guard : d16797 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28227 p hg
    simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28229 (p : Pattern) (guard : d16798 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28228 p hg
    simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28230 (p : Pattern) (guard : d5123 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28167 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28191 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28231 (p : Pattern) (guard : d5124 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5123 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28230 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28232 (p : Pattern) (guard : d5125 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28148 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5124 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28231 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28233 (p : Pattern) (guard : d5126 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5125 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28232 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28211 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28234 (p : Pattern) (guard : d5127 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5126 p = 1 := by simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28233 p hg
    simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28235 (p : Pattern) (guard : d5133 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5127 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28234 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28199 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28236 (p : Pattern) (guard : d5134 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28235 p hg
    simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28237 (p : Pattern) (guard : d5135 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28236 p hg
    simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28238 (p : Pattern) (guard : d5136 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28237 p hg
    simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28239 (p : Pattern) (guard : d5137 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28238 p hg
    simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28240 (p : Pattern) (guard : d5138 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28239 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28241 (p : Pattern) (guard : d1575 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28207 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28242 (p : Pattern) (guard : d1576 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28241 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27888 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28243 (p : Pattern) (guard : d1593 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28242 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28244 (p : Pattern) (guard : d10129 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1559 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28207 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28245 (p : Pattern) (guard : d10130 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10129 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28244 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27415 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28246 (p : Pattern) (guard : d10131 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10130 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28245 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28247 (p : Pattern) (guard : d10132 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28243 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10131 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28246 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28248 (p : Pattern) (guard : d10133 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10132 p = 1 := by simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28247 p hg
    simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28249 (p : Pattern) (guard : d10134 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10133 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28248 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
