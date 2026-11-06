import NetHack.Soko22Hazard87.Compare118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29750 (p : Pattern) (guard : d259211 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259210 p = 1 := by simpa only [d259211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29749 p hg
    simpa only [d259211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29751 (p : Pattern) (guard : d259212 p = 1) : d47768 p ≤ (-1 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259202 p = 1 := by simpa only [d259212, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29666 p hg
    simpa only [d259212, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259211 p = 1 := by simpa only [d259212, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29750 p hg
    simpa only [d259212, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29752 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29435 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29753 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29752 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29754 (p : Pattern) (guard : d30077 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29753 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29755 (p : Pattern) (guard : d30078 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29754 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29756 (p : Pattern) (guard : d257870 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29755 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29757 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29758 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29435 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29757 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29759 (p : Pattern) (guard : d257871 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29758 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29760 (p : Pattern) (guard : d257872 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29759 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29761 (p : Pattern) (guard : d257873 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29760 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29762 (p : Pattern) (guard : d257874 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29761 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29763 (p : Pattern) (guard : d257875 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29756 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29762 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29764 (p : Pattern) (guard : d257876 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29763 p hg
    simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29765 (p : Pattern) (guard : d259122 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29440 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29766 (p : Pattern) (guard : d259123 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259122 p = 1 := by simpa only [d259123, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29765 p hg
    simpa only [d259123, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259123, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d259123, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29767 (p : Pattern) (guard : d259124 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29764 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259123 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29766 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29768 (p : Pattern) (guard : d259213 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259124 p = 1 := by simpa only [d259213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29767 p hg
    simpa only [d259213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29769 (p : Pattern) (guard : d259125 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259124 p = 1 := by simpa only [d259125, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29588 p hg
    simpa only [d259125, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259125, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259125, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29770 (p : Pattern) (guard : d259214 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259213 p = 1 := by simpa only [d259214, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29768 p hg
    simpa only [d259214, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259125 p = 1 := by simpa only [d259214, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29769 p hg
    simpa only [d259214, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29771 (p : Pattern) (guard : d1999 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29449 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29772 (p : Pattern) (guard : d2000 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29771 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29773 (p : Pattern) (guard : d30077 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29772 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29774 (p : Pattern) (guard : d30078 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29773 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29775 (p : Pattern) (guard : d257870 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29774 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29776 (p : Pattern) (guard : d2013 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29231 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29777 (p : Pattern) (guard : d2014 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29449 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29776 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29778 (p : Pattern) (guard : d257871 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29777 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29779 (p : Pattern) (guard : d257872 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29778 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29780 (p : Pattern) (guard : d257873 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29779 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29781 (p : Pattern) (guard : d257874 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29780 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29782 (p : Pattern) (guard : d257875 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29775 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29781 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29783 (p : Pattern) (guard : d257876 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29782 p hg
    simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29784 (p : Pattern) (guard : d259122 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29454 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29785 (p : Pattern) (guard : d259123 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259122 p = 1 := by simpa only [d259123, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29784 p hg
    simpa only [d259123, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259123, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d259123, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29786 (p : Pattern) (guard : d259124 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29783 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259123 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29785 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29787 (p : Pattern) (guard : d259125 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259124 p = 1 := by simpa only [d259125, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29786 p hg
    simpa only [d259125, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259125, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259125, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29788 (p : Pattern) (guard : d259126 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259125 p = 1 := by simpa only [d259126, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29787 p hg
    simpa only [d259126, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259126, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259126, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29789 (p : Pattern) (guard : d259215 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259214 p = 1 := by simpa only [d259215, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29770 p hg
    simpa only [d259215, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259126 p = 1 := by simpa only [d259215, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29788 p hg
    simpa only [d259215, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29790 (p : Pattern) (guard : d259216 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259215 p = 1 := by simpa only [d259216, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29789 p hg
    simpa only [d259216, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259216, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259216, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29791 (p : Pattern) (guard : d259217 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259216 p = 1 := by simpa only [d259217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29790 p hg
    simpa only [d259217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259017 p = 1 := by simpa only [d259217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29463 p hg
    simpa only [d259217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29792 (p : Pattern) (guard : d259130 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259123 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29766 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29444 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29793 (p : Pattern) (guard : d259218 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259130 p = 1 := by simpa only [d259218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29792 p hg
    simpa only [d259218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29794 (p : Pattern) (guard : d259131 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259130 p = 1 := by simpa only [d259131, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d259131, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259131, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259131, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29795 (p : Pattern) (guard : d259219 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259218 p = 1 := by simpa only [d259219, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29793 p hg
    simpa only [d259219, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259131 p = 1 := by simpa only [d259219, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29794 p hg
    simpa only [d259219, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29796 (p : Pattern) (guard : d259130 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259123 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29785 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29458 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29797 (p : Pattern) (guard : d259131 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259130 p = 1 := by simpa only [d259131, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29796 p hg
    simpa only [d259131, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259131, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259131, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29798 (p : Pattern) (guard : d259132 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259131 p = 1 := by simpa only [d259132, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29797 p hg
    simpa only [d259132, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259132, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259132, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29799 (p : Pattern) (guard : d259220 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259219 p = 1 := by simpa only [d259220, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29795 p hg
    simpa only [d259220, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259132 p = 1 := by simpa only [d259220, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29798 p hg
    simpa only [d259220, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29800 (p : Pattern) (guard : d259221 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259220 p = 1 := by simpa only [d259221, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29799 p hg
    simpa only [d259221, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259221, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259221, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29801 (p : Pattern) (guard : d259222 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259221 p = 1 := by simpa only [d259222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29800 p hg
    simpa only [d259222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259022 p = 1 := by simpa only [d259222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29473 p hg
    simpa only [d259222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29802 (p : Pattern) (guard : d259223 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259217 p = 1 := by simpa only [d259223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29791 p hg
    simpa only [d259223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259222 p = 1 := by simpa only [d259223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29801 p hg
    simpa only [d259223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29803 (p : Pattern) (guard : d259224 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259223 p = 1 := by simpa only [d259224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29802 p hg
    simpa only [d259224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259024 p = 1 := by simpa only [d259224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29475 p hg
    simpa only [d259224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29804 (p : Pattern) (guard : d259225 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259225, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259225, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259224 p = 1 := by simpa only [d259225, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29803 p hg
    simpa only [d259225, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29805 (p : Pattern) (guard : d259226 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259226, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259226, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259225 p = 1 := by simpa only [d259226, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29804 p hg
    simpa only [d259226, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29806 (p : Pattern) (guard : d259227 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259023 p = 1 := by simpa only [d259227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29474 p hg
    simpa only [d259227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258747 p = 1 := by simpa only [d259227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29057 p hg
    simpa only [d259227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29807 (p : Pattern) (guard : d259228 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259024 p = 1 := by simpa only [d259228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29475 p hg
    simpa only [d259228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259227 p = 1 := by simpa only [d259228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29806 p hg
    simpa only [d259228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29808 (p : Pattern) (guard : d259229 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259229, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259229, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259228 p = 1 := by simpa only [d259229, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29807 p hg
    simpa only [d259229, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29809 (p : Pattern) (guard : d259230 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259230, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259230, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259229 p = 1 := by simpa only [d259230, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29808 p hg
    simpa only [d259230, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29810 (p : Pattern) (guard : d259231 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259226 p = 1 := by simpa only [d259231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29805 p hg
    simpa only [d259231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259230 p = 1 := by simpa only [d259231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29809 p hg
    simpa only [d259231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29811 (p : Pattern) (guard : d259232 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259231 p = 1 := by simpa only [d259232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29810 p hg
    simpa only [d259232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259028 p = 1 := by simpa only [d259232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29479 p hg
    simpa only [d259232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29812 (p : Pattern) (guard : d259233 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259232 p = 1 := by simpa only [d259233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29811 p hg
    simpa only [d259233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29813 (p : Pattern) (guard : d259234 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259233 p = 1 := by simpa only [d259234, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29812 p hg
    simpa only [d259234, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259234, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259234, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29814 (p : Pattern) (guard : d259235 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259235, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259235, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259234 p = 1 := by simpa only [d259235, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29813 p hg
    simpa only [d259235, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29815 (p : Pattern) (guard : d259236 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258877 p = 1 := by simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29249 p hg
    simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29816 (p : Pattern) (guard : d259237 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259028 p = 1 := by simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29479 p hg
    simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259236 p = 1 := by simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29815 p hg
    simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29817 (p : Pattern) (guard : d259238 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259237 p = 1 := by simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29816 p hg
    simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29818 (p : Pattern) (guard : d259239 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259238 p = 1 := by simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29817 p hg
    simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29819 (p : Pattern) (guard : d259240 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259239 p = 1 := by simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29818 p hg
    simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29820 (p : Pattern) (guard : d259241 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259235 p = 1 := by simpa only [d259241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29814 p hg
    simpa only [d259241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259240 p = 1 := by simpa only [d259241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29819 p hg
    simpa only [d259241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29821 (p : Pattern) (guard : d259242 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259241 p = 1 := by simpa only [d259242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29820 p hg
    simpa only [d259242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29822 (p : Pattern) (guard : d259243 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259242 p = 1 := by simpa only [d259243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29821 p hg
    simpa only [d259243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29823 (p : Pattern) (guard : d259244 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259243 p = 1 := by simpa only [d259244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29822 p hg
    simpa only [d259244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29824 (p : Pattern) (guard : d259245 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259236 p = 1 := by simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29815 p hg
    simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29825 (p : Pattern) (guard : d259246 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259245 p = 1 := by simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29824 p hg
    simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29826 (p : Pattern) (guard : d259247 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259246 p = 1 := by simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29825 p hg
    simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29827 (p : Pattern) (guard : d259248 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259247 p = 1 := by simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29826 p hg
    simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29828 (p : Pattern) (guard : d259249 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259240 p = 1 := by simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29819 p hg
    simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259248 p = 1 := by simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29827 p hg
    simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29829 (p : Pattern) (guard : d259250 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259249 p = 1 := by simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29828 p hg
    simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29830 (p : Pattern) (guard : d259251 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259250 p = 1 := by simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29829 p hg
    simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29831 (p : Pattern) (guard : d259252 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259251 p = 1 := by simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29830 p hg
    simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29832 (p : Pattern) (guard : d259253 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259244 p = 1 := by simpa only [d259253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29823 p hg
    simpa only [d259253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259252 p = 1 := by simpa only [d259253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29831 p hg
    simpa only [d259253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29833 (p : Pattern) (guard : d259254 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259253 p = 1 := by simpa only [d259254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29832 p hg
    simpa only [d259254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29834 (p : Pattern) (guard : d259255 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259240 p = 1 := by simpa only [d259255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29819 p hg
    simpa only [d259255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29835 (p : Pattern) (guard : d259256 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259255 p = 1 := by simpa only [d259256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29834 p hg
    simpa only [d259256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29836 (p : Pattern) (guard : d259257 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259256 p = 1 := by simpa only [d259257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29835 p hg
    simpa only [d259257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29837 (p : Pattern) (guard : d259258 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259257 p = 1 := by simpa only [d259258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29836 p hg
    simpa only [d259258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29838 (p : Pattern) (guard : d259259 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259258 p = 1 := by simpa only [d259259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29837 p hg
    simpa only [d259259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29839 (p : Pattern) (guard : d259260 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259259 p = 1 := by simpa only [d259260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29838 p hg
    simpa only [d259260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29840 (p : Pattern) (guard : d259261 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259254 p = 1 := by simpa only [d259261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29833 p hg
    simpa only [d259261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259260 p = 1 := by simpa only [d259261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29839 p hg
    simpa only [d259261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29841 (p : Pattern) (guard : d259262 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259261 p = 1 := by simpa only [d259262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29840 p hg
    simpa only [d259262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29842 (p : Pattern) (guard : d259263 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259262 p = 1 := by simpa only [d259263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29841 p hg
    simpa only [d259263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29843 (p : Pattern) (guard : d259264 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259264, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259264, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259263 p = 1 := by simpa only [d259264, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29842 p hg
    simpa only [d259264, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29844 (p : Pattern) (guard : d259265 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259264 p = 1 := by simpa only [d259265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29843 p hg
    simpa only [d259265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29845 (p : Pattern) (guard : d259266 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259248 p = 1 := by simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29827 p hg
    simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29846 (p : Pattern) (guard : d259267 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259266 p = 1 := by simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29845 p hg
    simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29847 (p : Pattern) (guard : d259268 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259267 p = 1 := by simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29846 p hg
    simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29848 (p : Pattern) (guard : d259269 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259268 p = 1 := by simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29847 p hg
    simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29849 (p : Pattern) (guard : d259270 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259269 p = 1 := by simpa only [d259270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29848 p hg
    simpa only [d259270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29850 (p : Pattern) (guard : d259271 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259270 p = 1 := by simpa only [d259271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29849 p hg
    simpa only [d259271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29851 (p : Pattern) (guard : d259272 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259271 p = 1 := by simpa only [d259272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29850 p hg
    simpa only [d259272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29852 (p : Pattern) (guard : d259273 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259272 p = 1 := by simpa only [d259273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29851 p hg
    simpa only [d259273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29853 (p : Pattern) (guard : d259274 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259273 p = 1 := by simpa only [d259274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29852 p hg
    simpa only [d259274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29854 (p : Pattern) (guard : d259275 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259275, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259275, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259274 p = 1 := by simpa only [d259275, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29853 p hg
    simpa only [d259275, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29855 (p : Pattern) (guard : d259276 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259275 p = 1 := by simpa only [d259276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29854 p hg
    simpa only [d259276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29856 (p : Pattern) (guard : d259277 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259265 p = 1 := by simpa only [d259277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29844 p hg
    simpa only [d259277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259276 p = 1 := by simpa only [d259277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29855 p hg
    simpa only [d259277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29857 (p : Pattern) (guard : d259278 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259277 p = 1 := by simpa only [d259278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29856 p hg
    simpa only [d259278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29858 (p : Pattern) (guard : d259279 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259278 p = 1 := by simpa only [d259279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29857 p hg
    simpa only [d259279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29859 (p : Pattern) (guard : d259280 p = 1) : d47865 p ≤ (-1 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259279 p = 1 := by simpa only [d259280, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29858 p hg
    simpa only [d259280, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259280, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29083 p hg
    simpa only [d259280, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29860 (p : Pattern) (guard : d259281 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d259212 p = 1 := by simpa only [d259281, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29751 p hg
    simpa only [d259281, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259280 p = 1 := by simpa only [d259281, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29859 p hg
    simpa only [d259281, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29861 (p : Pattern) (guard : d259282 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259281 p = 1 := by simpa only [d259282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29860 p hg
    simpa only [d259282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29862 (p : Pattern) (guard : d259283 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259282 p = 1 := by simpa only [d259283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29861 p hg
    simpa only [d259283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29863 (p : Pattern) (guard : d259284 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259283 p = 1 := by simpa only [d259284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29862 p hg
    simpa only [d259284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29864 (p : Pattern) (guard : d259285 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259284 p = 1 := by simpa only [d259285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29863 p hg
    simpa only [d259285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29865 (p : Pattern) (guard : d259286 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259285 p = 1 := by simpa only [d259286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29864 p hg
    simpa only [d259286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29866 (p : Pattern) (guard : d259287 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259286 p = 1 := by simpa only [d259287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29865 p hg
    simpa only [d259287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29867 (p : Pattern) (guard : d259288 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259287 p = 1 := by simpa only [d259288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29866 p hg
    simpa only [d259288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29868 (p : Pattern) (guard : d259289 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259288 p = 1 := by simpa only [d259289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29867 p hg
    simpa only [d259289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29869 (p : Pattern) (guard : d259290 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d259068 p = 1 := by simpa only [d259290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29519 p hg
    simpa only [d259290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259289 p = 1 := by simpa only [d259290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29868 p hg
    simpa only [d259290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29870 (p : Pattern) (guard : d259291 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29583 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29871 (p : Pattern) (guard : d259292 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29870 p hg
    simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29872 (p : Pattern) (guard : d259293 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29585 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29871 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29873 (p : Pattern) (guard : d259294 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29872 p hg
    simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29874 (p : Pattern) (guard : d259295 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259294 p = 1 := by simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29873 p hg
    simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29875 (p : Pattern) (guard : d259296 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259295 p = 1 := by simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29874 p hg
    simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29876 (p : Pattern) (guard : d259297 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259296 p = 1 := by simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29875 p hg
    simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29877 (p : Pattern) (guard : d2027 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29578 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29878 (p : Pattern) (guard : d2028 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29877 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29879 (p : Pattern) (guard : d2029 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29878 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29880 (p : Pattern) (guard : d2030 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29879 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29881 (p : Pattern) (guard : d27032 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29880 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29882 (p : Pattern) (guard : d259298 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29583 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29881 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29883 (p : Pattern) (guard : d259299 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29882 p hg
    simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29884 (p : Pattern) (guard : d259300 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29881 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29885 (p : Pattern) (guard : d259301 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29884 p hg
    simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29886 (p : Pattern) (guard : d259302 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29883 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29885 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29887 (p : Pattern) (guard : d259303 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29886 p hg
    simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29888 (p : Pattern) (guard : d259304 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259303 p = 1 := by simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29887 p hg
    simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29889 (p : Pattern) (guard : d259305 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259304 p = 1 := by simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29888 p hg
    simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29890 (p : Pattern) (guard : d259306 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259305 p = 1 := by simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29889 p hg
    simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29891 (p : Pattern) (guard : d259307 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259297 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29876 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259306 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29890 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29892 (p : Pattern) (guard : d259308 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29871 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29885 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29893 (p : Pattern) (guard : d259309 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29892 p hg
    simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29894 (p : Pattern) (guard : d259310 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259309 p = 1 := by simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29893 p hg
    simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29895 (p : Pattern) (guard : d259311 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259310 p = 1 := by simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29894 p hg
    simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29896 (p : Pattern) (guard : d259312 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259311 p = 1 := by simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29895 p hg
    simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29897 (p : Pattern) (guard : d259313 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29885 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28913 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29898 (p : Pattern) (guard : d259314 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29897 p hg
    simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29899 (p : Pattern) (guard : d259315 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259314 p = 1 := by simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29898 p hg
    simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29900 (p : Pattern) (guard : d259316 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259315 p = 1 := by simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29899 p hg
    simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29901 (p : Pattern) (guard : d259317 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259316 p = 1 := by simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29900 p hg
    simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29902 (p : Pattern) (guard : d259318 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259312 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29896 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29903 (p : Pattern) (guard : d259319 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259307 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29891 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259318 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29904 (p : Pattern) (guard : d259320 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259306 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29890 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29905 (p : Pattern) (guard : d259321 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259317 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29906 (p : Pattern) (guard : d259322 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259320 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29904 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259321 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29907 (p : Pattern) (guard : d259323 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259319 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29903 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259322 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29906 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29908 (p : Pattern) (guard : d259324 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259323 p = 1 := by simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29907 p hg
    simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29909 (p : Pattern) (guard : d259325 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259324 p = 1 := by simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29908 p hg
    simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29910 (p : Pattern) (guard : d259326 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259321 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29911 (p : Pattern) (guard : d259327 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259322 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29906 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259326 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29910 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29912 (p : Pattern) (guard : d259328 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259327 p = 1 := by simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29911 p hg
    simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29913 (p : Pattern) (guard : d259329 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259328 p = 1 := by simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29912 p hg
    simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29914 (p : Pattern) (guard : d259330 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259325 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29909 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259329 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29913 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29915 (p : Pattern) (guard : d259331 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259329 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29913 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29916 (p : Pattern) (guard : d259332 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259330 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29914 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259331 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29915 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29917 (p : Pattern) (guard : d259333 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259332 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29916 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29918 (p : Pattern) (guard : d259334 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259333 p = 1 := by simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29917 p hg
    simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29919 (p : Pattern) (guard : d259335 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259334 p = 1 := by simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29918 p hg
    simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29920 (p : Pattern) (guard : d259336 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259331 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29915 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29921 (p : Pattern) (guard : d259337 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259336 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29920 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29922 (p : Pattern) (guard : d259338 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259337 p = 1 := by simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29921 p hg
    simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29923 (p : Pattern) (guard : d259339 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259338 p = 1 := by simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29922 p hg
    simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29924 (p : Pattern) (guard : d259340 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259335 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29919 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259339 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29923 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29925 (p : Pattern) (guard : d259341 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259340 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29924 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29926 (p : Pattern) (guard : d259342 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259341 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29925 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29927 (p : Pattern) (guard : d259343 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259342 p = 1 := by simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29926 p hg
    simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29928 (p : Pattern) (guard : d259344 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259339 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29923 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29929 (p : Pattern) (guard : d259345 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259344 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29928 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29930 (p : Pattern) (guard : d259346 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259345 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29929 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29931 (p : Pattern) (guard : d259347 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259346 p = 1 := by simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29930 p hg
    simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29932 (p : Pattern) (guard : d259348 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259343 p = 1 := by simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29927 p hg
    simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259347 p = 1 := by simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29931 p hg
    simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29933 (p : Pattern) (guard : d259349 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259348 p = 1 := by simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29932 p hg
    simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29934 (p : Pattern) (guard : d259350 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259349 p = 1 := by simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29933 p hg
    simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29935 (p : Pattern) (guard : d259351 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259350 p = 1 := by simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29934 p hg
    simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29936 (p : Pattern) (guard : d259352 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259351 p = 1 := by simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29935 p hg
    simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29937 (p : Pattern) (guard : d259353 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259352 p = 1 := by simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29936 p hg
    simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29938 (p : Pattern) (guard : d259354 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259353 p = 1 := by simpa only [d259354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29937 p hg
    simpa only [d259354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29939 (p : Pattern) (guard : d259355 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259354 p = 1 := by simpa only [d259355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29938 p hg
    simpa only [d259355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29940 (p : Pattern) (guard : d259356 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259342 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29926 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29941 (p : Pattern) (guard : d259357 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259346 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29930 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29942 (p : Pattern) (guard : d259358 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259356 p = 1 := by simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29940 p hg
    simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259357 p = 1 := by simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29941 p hg
    simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29943 (p : Pattern) (guard : d259359 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259358 p = 1 := by simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29942 p hg
    simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29944 (p : Pattern) (guard : d259360 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259359 p = 1 := by simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29943 p hg
    simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29945 (p : Pattern) (guard : d259361 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259360 p = 1 := by simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29944 p hg
    simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29946 (p : Pattern) (guard : d259362 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259361 p = 1 := by simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29945 p hg
    simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29947 (p : Pattern) (guard : d259363 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259352 p = 1 := by simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29936 p hg
    simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259362 p = 1 := by simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29946 p hg
    simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29948 (p : Pattern) (guard : d259364 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259353 p = 1 := by simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29937 p hg
    simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259363 p = 1 := by simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29947 p hg
    simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29949 (p : Pattern) (guard : d259365 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259364 p = 1 := by simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29948 p hg
    simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29950 (p : Pattern) (guard : d259366 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259355 p = 1 := by simpa only [d259366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29939 p hg
    simpa only [d259366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259365 p = 1 := by simpa only [d259366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29949 p hg
    simpa only [d259366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29951 (p : Pattern) (guard : d259367 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259341 p = 1 := by simpa only [d259367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29925 p hg
    simpa only [d259367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29952 (p : Pattern) (guard : d259368 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259367 p = 1 := by simpa only [d259368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29951 p hg
    simpa only [d259368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29953 (p : Pattern) (guard : d259369 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259345 p = 1 := by simpa only [d259369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29929 p hg
    simpa only [d259369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29954 (p : Pattern) (guard : d259370 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259369 p = 1 := by simpa only [d259370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29953 p hg
    simpa only [d259370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29955 (p : Pattern) (guard : d259371 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259368 p = 1 := by simpa only [d259371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29952 p hg
    simpa only [d259371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259370 p = 1 := by simpa only [d259371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29954 p hg
    simpa only [d259371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29956 (p : Pattern) (guard : d259372 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259371 p = 1 := by simpa only [d259372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29955 p hg
    simpa only [d259372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29957 (p : Pattern) (guard : d259373 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259372 p = 1 := by simpa only [d259373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29956 p hg
    simpa only [d259373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29958 (p : Pattern) (guard : d259374 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259373 p = 1 := by simpa only [d259374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29957 p hg
    simpa only [d259374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29959 (p : Pattern) (guard : d259375 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259340 p = 1 := by simpa only [d259375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29924 p hg
    simpa only [d259375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29960 (p : Pattern) (guard : d259376 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259375 p = 1 := by simpa only [d259376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29959 p hg
    simpa only [d259376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29961 (p : Pattern) (guard : d259377 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259376 p = 1 := by simpa only [d259377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29960 p hg
    simpa only [d259377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29962 (p : Pattern) (guard : d259378 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259344 p = 1 := by simpa only [d259378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29928 p hg
    simpa only [d259378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29963 (p : Pattern) (guard : d259379 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259378 p = 1 := by simpa only [d259379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29962 p hg
    simpa only [d259379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29964 (p : Pattern) (guard : d259380 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259379 p = 1 := by simpa only [d259380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29963 p hg
    simpa only [d259380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29965 (p : Pattern) (guard : d259381 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259377 p = 1 := by simpa only [d259381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29961 p hg
    simpa only [d259381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259380 p = 1 := by simpa only [d259381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29964 p hg
    simpa only [d259381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29966 (p : Pattern) (guard : d259382 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259381 p = 1 := by simpa only [d259382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29965 p hg
    simpa only [d259382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29967 (p : Pattern) (guard : d259383 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259382 p = 1 := by simpa only [d259383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29966 p hg
    simpa only [d259383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29968 (p : Pattern) (guard : d258183 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29577 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29969 (p : Pattern) (guard : d258184 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29968 p hg
    simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29970 (p : Pattern) (guard : d258185 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28913 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29969 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29971 (p : Pattern) (guard : d258186 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29970 p hg
    simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29972 (p : Pattern) (guard : d258187 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258186 p = 1 := by simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29971 p hg
    simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29973 (p : Pattern) (guard : d258188 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258187 p = 1 := by simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29972 p hg
    simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29974 (p : Pattern) (guard : d258189 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258188 p = 1 := by simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29973 p hg
    simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29975 (p : Pattern) (guard : d259384 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258189 p = 1 := by simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29974 p hg
    simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259297 p = 1 := by simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29876 p hg
    simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29976 (p : Pattern) (guard : d259385 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29969 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29871 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29977 (p : Pattern) (guard : d259386 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259385 p = 1 := by simpa only [d259386, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29976 p hg
    simpa only [d259386, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259386, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259386, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29978 (p : Pattern) (guard : d259387 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259386 p = 1 := by simpa only [d259387, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29977 p hg
    simpa only [d259387, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259387, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259387, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29979 (p : Pattern) (guard : d259388 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259388, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259388, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259387 p = 1 := by simpa only [d259388, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29978 p hg
    simpa only [d259388, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29980 (p : Pattern) (guard : d259389 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259388 p = 1 := by simpa only [d259389, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29979 p hg
    simpa only [d259389, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259389, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259389, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29981 (p : Pattern) (guard : d259390 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259389 p = 1 := by simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29980 p hg
    simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259312 p = 1 := by simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29896 p hg
    simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29982 (p : Pattern) (guard : d259391 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259384 p = 1 := by simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29975 p hg
    simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259390 p = 1 := by simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29981 p hg
    simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29983 (p : Pattern) (guard : d259392 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259391 p = 1 := by simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29982 p hg
    simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259319 p = 1 := by simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29903 p hg
    simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29984 (p : Pattern) (guard : d259393 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259393, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259393, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259392 p = 1 := by simpa only [d259393, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29983 p hg
    simpa only [d259393, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29985 (p : Pattern) (guard : d259394 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259394, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259394, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259393 p = 1 := by simpa only [d259394, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29984 p hg
    simpa only [d259394, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29986 (p : Pattern) (guard : d259395 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259318 p = 1 := by simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259321 p = 1 := by simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29987 (p : Pattern) (guard : d259396 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259319 p = 1 := by simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29903 p hg
    simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259395 p = 1 := by simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29986 p hg
    simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29988 (p : Pattern) (guard : d259397 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259397, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259397, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259396 p = 1 := by simpa only [d259397, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29987 p hg
    simpa only [d259397, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29989 (p : Pattern) (guard : d259398 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259398, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259398, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259397 p = 1 := by simpa only [d259398, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29988 p hg
    simpa only [d259398, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29990 (p : Pattern) (guard : d259399 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259394 p = 1 := by simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29985 p hg
    simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259398 p = 1 := by simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29989 p hg
    simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29991 (p : Pattern) (guard : d259400 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259399 p = 1 := by simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29990 p hg
    simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259330 p = 1 := by simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29914 p hg
    simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29992 (p : Pattern) (guard : d259401 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259400 p = 1 := by simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29991 p hg
    simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29993 (p : Pattern) (guard : d259402 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259401 p = 1 := by simpa only [d259402, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29992 p hg
    simpa only [d259402, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259402, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259402, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29994 (p : Pattern) (guard : d259403 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259403, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259403, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259402 p = 1 := by simpa only [d259403, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29993 p hg
    simpa only [d259403, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29995 (p : Pattern) (guard : d259404 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259403 p = 1 := by simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29994 p hg
    simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259335 p = 1 := by simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29919 p hg
    simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29996 (p : Pattern) (guard : d259405 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259404 p = 1 := by simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29995 p hg
    simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29997 (p : Pattern) (guard : d259406 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259405 p = 1 := by simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29996 p hg
    simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29998 (p : Pattern) (guard : d259407 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259406 p = 1 := by simpa only [d259407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29997 p hg
    simpa only [d259407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29999 (p : Pattern) (guard : d259408 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259407 p = 1 := by simpa only [d259408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29998 p hg
    simpa only [d259408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259343 p = 1 := by simpa only [d259408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29927 p hg
    simpa only [d259408, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
