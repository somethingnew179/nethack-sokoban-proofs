import NetHack.Soko22Hazard87.Compare125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31500 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31054 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31501 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31233 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31500 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31502 (p : Pattern) (guard : d257871 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31501 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31503 (p : Pattern) (guard : d257872 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31502 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31504 (p : Pattern) (guard : d257873 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31503 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31505 (p : Pattern) (guard : d257874 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31504 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31506 (p : Pattern) (guard : d257875 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31499 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31505 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31507 (p : Pattern) (guard : d257876 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31506 p hg
    simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d257876, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31508 (p : Pattern) (guard : d259291 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31505 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31509 (p : Pattern) (guard : d259292 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31508 p hg
    simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31510 (p : Pattern) (guard : d259293 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31507 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31509 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31511 (p : Pattern) (guard : d259468 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259293 p = 1 := by simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31510 p hg
    simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31512 (p : Pattern) (guard : d259294 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31331 p hg
    simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31513 (p : Pattern) (guard : d259469 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259468 p = 1 := by simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31511 p hg
    simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259294 p = 1 := by simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31512 p hg
    simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31514 (p : Pattern) (guard : d1999 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31247 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31515 (p : Pattern) (guard : d2000 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31514 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31516 (p : Pattern) (guard : d30077 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31515 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31517 (p : Pattern) (guard : d30078 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31516 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31518 (p : Pattern) (guard : d257870 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31517 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31519 (p : Pattern) (guard : d2013 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31068 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31520 (p : Pattern) (guard : d2014 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31247 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31519 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31521 (p : Pattern) (guard : d257871 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31520 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31522 (p : Pattern) (guard : d257872 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31521 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31523 (p : Pattern) (guard : d257873 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31522 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31524 (p : Pattern) (guard : d257874 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31523 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31525 (p : Pattern) (guard : d257875 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31518 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31524 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31526 (p : Pattern) (guard : d257876 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31525 p hg
    simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d257876, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31527 (p : Pattern) (guard : d259291 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31524 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31528 (p : Pattern) (guard : d259292 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31527 p hg
    simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31529 (p : Pattern) (guard : d259293 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31526 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31528 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31530 (p : Pattern) (guard : d259294 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31529 p hg
    simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31531 (p : Pattern) (guard : d259295 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259294 p = 1 := by simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31530 p hg
    simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31532 (p : Pattern) (guard : d259470 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259469 p = 1 := by simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31513 p hg
    simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259295 p = 1 := by simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31531 p hg
    simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31533 (p : Pattern) (guard : d259471 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259470 p = 1 := by simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31532 p hg
    simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31534 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31500 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31535 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31534 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31536 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31535 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31537 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31536 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31538 (p : Pattern) (guard : d27032 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31537 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31539 (p : Pattern) (guard : d259298 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31505 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31538 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31540 (p : Pattern) (guard : d259299 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31539 p hg
    simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31541 (p : Pattern) (guard : d259300 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31538 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31542 (p : Pattern) (guard : d259301 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31541 p hg
    simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31543 (p : Pattern) (guard : d259302 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31540 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31542 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31544 (p : Pattern) (guard : d259483 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259302 p = 1 := by simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31543 p hg
    simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31545 (p : Pattern) (guard : d259303 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31345 p hg
    simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31546 (p : Pattern) (guard : d259484 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259483 p = 1 := by simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31544 p hg
    simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259303 p = 1 := by simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31545 p hg
    simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31547 (p : Pattern) (guard : d2027 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31519 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31548 (p : Pattern) (guard : d2028 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31547 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31549 (p : Pattern) (guard : d2029 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31548 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31550 (p : Pattern) (guard : d2030 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31549 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31551 (p : Pattern) (guard : d27032 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31550 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31552 (p : Pattern) (guard : d259298 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31524 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31551 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31553 (p : Pattern) (guard : d259299 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31552 p hg
    simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31554 (p : Pattern) (guard : d259300 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31551 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31555 (p : Pattern) (guard : d259301 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31554 p hg
    simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31556 (p : Pattern) (guard : d259302 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31553 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31555 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31557 (p : Pattern) (guard : d259303 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31556 p hg
    simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31558 (p : Pattern) (guard : d259304 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259303 p = 1 := by simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31557 p hg
    simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31559 (p : Pattern) (guard : d259485 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259484 p = 1 := by simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31546 p hg
    simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259304 p = 1 := by simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31558 p hg
    simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31560 (p : Pattern) (guard : d259486 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259485 p = 1 := by simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31559 p hg
    simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31561 (p : Pattern) (guard : d259487 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259471 p = 1 := by simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31533 p hg
    simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259486 p = 1 := by simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31560 p hg
    simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31562 (p : Pattern) (guard : d259308 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31509 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31542 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31563 (p : Pattern) (guard : d259477 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259308 p = 1 := by simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31562 p hg
    simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31564 (p : Pattern) (guard : d259309 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31351 p hg
    simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31565 (p : Pattern) (guard : d259478 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259477 p = 1 := by simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31563 p hg
    simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259309 p = 1 := by simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31564 p hg
    simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31566 (p : Pattern) (guard : d259308 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31528 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31555 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31567 (p : Pattern) (guard : d259309 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31566 p hg
    simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31568 (p : Pattern) (guard : d259310 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259309 p = 1 := by simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31567 p hg
    simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31569 (p : Pattern) (guard : d259479 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259478 p = 1 := by simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31565 p hg
    simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259310 p = 1 := by simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31568 p hg
    simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31570 (p : Pattern) (guard : d259480 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259479 p = 1 := by simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31569 p hg
    simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31571 (p : Pattern) (guard : d259313 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31542 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31572 (p : Pattern) (guard : d259488 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259313 p = 1 := by simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31571 p hg
    simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31573 (p : Pattern) (guard : d259314 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31356 p hg
    simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31574 (p : Pattern) (guard : d259489 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259488 p = 1 := by simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31572 p hg
    simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259314 p = 1 := by simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31573 p hg
    simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31575 (p : Pattern) (guard : d259313 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31555 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30923 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31576 (p : Pattern) (guard : d259314 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31575 p hg
    simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31577 (p : Pattern) (guard : d259315 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259314 p = 1 := by simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31576 p hg
    simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31578 (p : Pattern) (guard : d259490 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259489 p = 1 := by simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31574 p hg
    simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259315 p = 1 := by simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31577 p hg
    simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31579 (p : Pattern) (guard : d259491 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259490 p = 1 := by simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31578 p hg
    simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31580 (p : Pattern) (guard : d259492 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259480 p = 1 := by simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31570 p hg
    simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259491 p = 1 := by simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31579 p hg
    simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31581 (p : Pattern) (guard : d259493 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259487 p = 1 := by simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31561 p hg
    simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259492 p = 1 := by simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31580 p hg
    simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31582 (p : Pattern) (guard : d259503 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259486 p = 1 := by simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31560 p hg
    simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259491 p = 1 := by simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31579 p hg
    simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31583 (p : Pattern) (guard : d259497 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259491 p = 1 := by simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31579 p hg
    simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31584 (p : Pattern) (guard : d259504 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259503 p = 1 := by simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31582 p hg
    simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259497 p = 1 := by simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31583 p hg
    simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31585 (p : Pattern) (guard : d259505 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259493 p = 1 := by simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31581 p hg
    simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259504 p = 1 := by simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31584 p hg
    simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31586 (p : Pattern) (guard : d259506 p = 1) : d47804 p ≤ (-2 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259505 p = 1 := by simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31585 p hg
    simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31587 (p : Pattern) (guard : d259507 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259506 p = 1 := by simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31586 p hg
    simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31588 (p : Pattern) (guard : d259508 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259497 p = 1 := by simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31583 p hg
    simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31589 (p : Pattern) (guard : d259509 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259504 p = 1 := by simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31584 p hg
    simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259508 p = 1 := by simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31588 p hg
    simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31590 (p : Pattern) (guard : d259510 p = 1) : d47804 p ≤ (-2 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259509 p = 1 := by simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31589 p hg
    simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31591 (p : Pattern) (guard : d259511 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259510 p = 1 := by simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31590 p hg
    simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31592 (p : Pattern) (guard : d259512 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259507 p = 1 := by simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31587 p hg
    simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259511 p = 1 := by simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31591 p hg
    simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31593 (p : Pattern) (guard : d259517 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259511 p = 1 := by simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31591 p hg
    simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31594 (p : Pattern) (guard : d259518 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259512 p = 1 := by simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31592 p hg
    simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259517 p = 1 := by simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31593 p hg
    simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31595 (p : Pattern) (guard : d259519 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259518 p = 1 := by simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31594 p hg
    simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31596 (p : Pattern) (guard : d259520 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259519 p = 1 := by simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31595 p hg
    simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31597 (p : Pattern) (guard : d259521 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259520 p = 1 := by simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31596 p hg
    simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31598 (p : Pattern) (guard : d259526 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259517 p = 1 := by simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31593 p hg
    simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31599 (p : Pattern) (guard : d259527 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259526 p = 1 := by simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31598 p hg
    simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31600 (p : Pattern) (guard : d259528 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259527 p = 1 := by simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31599 p hg
    simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31601 (p : Pattern) (guard : d259529 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259528 p = 1 := by simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31600 p hg
    simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31602 (p : Pattern) (guard : d259530 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259521 p = 1 := by simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31597 p hg
    simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259529 p = 1 := by simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31601 p hg
    simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31603 (p : Pattern) (guard : d259531 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259530 p = 1 := by simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31602 p hg
    simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31604 (p : Pattern) (guard : d259532 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259531 p = 1 := by simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31603 p hg
    simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31605 (p : Pattern) (guard : d259533 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259532 p = 1 := by simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31604 p hg
    simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31606 (p : Pattern) (guard : d259547 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259529 p = 1 := by simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31601 p hg
    simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31607 (p : Pattern) (guard : d259548 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259547 p = 1 := by simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31606 p hg
    simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31608 (p : Pattern) (guard : d259549 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259548 p = 1 := by simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31607 p hg
    simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31609 (p : Pattern) (guard : d259550 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259549 p = 1 := by simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31608 p hg
    simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31610 (p : Pattern) (guard : d260169 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259533 p = 1 := by simpa only [d260169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31605 p hg
    simpa only [d260169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259550 p = 1 := by simpa only [d260169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31609 p hg
    simpa only [d260169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31611 (p : Pattern) (guard : d260170 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260169 p = 1 := by simpa only [d260170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31610 p hg
    simpa only [d260170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31612 (p : Pattern) (guard : d260171 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d260170 p = 1 := by simpa only [d260171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31611 p hg
    simpa only [d260171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31613 (p : Pattern) (guard : d260172 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260171 p = 1 := by simpa only [d260172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31612 p hg
    simpa only [d260172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31614 (p : Pattern) (guard : d260173 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260172 p = 1 := by simpa only [d260173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31613 p hg
    simpa only [d260173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31615 (p : Pattern) (guard : d260174 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260174, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260174, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260173 p = 1 := by simpa only [d260174, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31614 p hg
    simpa only [d260174, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31616 (p : Pattern) (guard : d260175 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260174 p = 1 := by simpa only [d260175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31615 p hg
    simpa only [d260175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31617 (p : Pattern) (guard : d260176 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260175 p = 1 := by simpa only [d260176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31616 p hg
    simpa only [d260176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31618 (p : Pattern) (guard : d260177 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260176 p = 1 := by simpa only [d260177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31617 p hg
    simpa only [d260177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31619 (p : Pattern) (guard : d260178 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260177 p = 1 := by simpa only [d260178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31618 p hg
    simpa only [d260178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31620 (p : Pattern) (guard : d260179 p = 1) : d47865 p ≤ (-2 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260178 p = 1 := by simpa only [d260179, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31619 p hg
    simpa only [d260179, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260179, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30957 p hg
    simpa only [d260179, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31621 (p : Pattern) (guard : d260180 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d260168 p = 1 := by simpa only [d260180, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31494 p hg
    simpa only [d260180, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260179 p = 1 := by simpa only [d260180, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31620 p hg
    simpa only [d260180, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31622 (p : Pattern) (guard : d260181 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260180 p = 1 := by simpa only [d260181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31621 p hg
    simpa only [d260181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31623 (p : Pattern) (guard : d260182 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260181 p = 1 := by simpa only [d260182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31622 p hg
    simpa only [d260182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31624 (p : Pattern) (guard : d260183 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260182 p = 1 := by simpa only [d260183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31623 p hg
    simpa only [d260183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31625 (p : Pattern) (guard : d260184 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260183 p = 1 := by simpa only [d260184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31624 p hg
    simpa only [d260184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31626 (p : Pattern) (guard : d260185 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260184 p = 1 := by simpa only [d260185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31625 p hg
    simpa only [d260185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31627 (p : Pattern) (guard : d260186 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260185 p = 1 := by simpa only [d260186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31626 p hg
    simpa only [d260186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31628 (p : Pattern) (guard : d260187 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260186 p = 1 := by simpa only [d260187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31627 p hg
    simpa only [d260187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31629 (p : Pattern) (guard : d260188 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260187 p = 1 := by simpa only [d260188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31628 p hg
    simpa only [d260188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31630 (p : Pattern) (guard : d260189 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260188 p = 1 := by simpa only [d260189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d260189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31631 (p : Pattern) (guard : d260190 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d260160 p = 1 := by simpa only [d260190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31315 p hg
    simpa only [d260190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260189 p = 1 := by simpa only [d260190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31630 p hg
    simpa only [d260190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31632 (p : Pattern) (guard : d258183 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31320 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31633 (p : Pattern) (guard : d258184 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31632 p hg
    simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d258184, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31634 (p : Pattern) (guard : d258185 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30787 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31633 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31635 (p : Pattern) (guard : d258186 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31634 p hg
    simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d258186, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31636 (p : Pattern) (guard : d258187 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258186 p = 1 := by simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31635 p hg
    simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d258187, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31637 (p : Pattern) (guard : d258188 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258187 p = 1 := by simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31636 p hg
    simpa only [d258188, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31638 (p : Pattern) (guard : d258189 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258188 p = 1 := by simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31637 p hg
    simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d258189, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31639 (p : Pattern) (guard : d259573 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30969 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31640 (p : Pattern) (guard : d259574 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31639 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31641 (p : Pattern) (guard : d259575 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31323 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31640 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31642 (p : Pattern) (guard : d259576 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30780 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31643 (p : Pattern) (guard : d259577 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31641 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31642 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31644 (p : Pattern) (guard : d259578 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31643 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31645 (p : Pattern) (guard : d259579 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31644 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31646 (p : Pattern) (guard : d259580 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31645 p hg
    simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31647 (p : Pattern) (guard : d259581 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31633 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31646 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31648 (p : Pattern) (guard : d259582 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31647 p hg
    simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31649 (p : Pattern) (guard : d259583 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259582 p = 1 := by simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31648 p hg
    simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31650 (p : Pattern) (guard : d259584 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259583 p = 1 := by simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31649 p hg
    simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31651 (p : Pattern) (guard : d259585 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259584 p = 1 := by simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31650 p hg
    simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31652 (p : Pattern) (guard : d259586 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258189 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31638 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259585 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31651 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31653 (p : Pattern) (guard : d259587 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31646 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30787 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31654 (p : Pattern) (guard : d259588 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31653 p hg
    simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31655 (p : Pattern) (guard : d259589 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259588 p = 1 := by simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31654 p hg
    simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31656 (p : Pattern) (guard : d259590 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259589 p = 1 := by simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31655 p hg
    simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31657 (p : Pattern) (guard : d259591 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259590 p = 1 := by simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31656 p hg
    simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31658 (p : Pattern) (guard : d259592 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31651 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259591 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31657 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31659 (p : Pattern) (guard : d259593 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259586 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31652 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259592 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31658 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31660 (p : Pattern) (guard : d259594 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31644 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31340 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31661 (p : Pattern) (guard : d259595 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31660 p hg
    simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31662 (p : Pattern) (guard : d259596 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31661 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30787 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31663 (p : Pattern) (guard : d259597 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31662 p hg
    simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31664 (p : Pattern) (guard : d259598 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259597 p = 1 := by simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31663 p hg
    simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31665 (p : Pattern) (guard : d259599 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259598 p = 1 := by simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31664 p hg
    simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31666 (p : Pattern) (guard : d259600 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259599 p = 1 := by simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31665 p hg
    simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31667 (p : Pattern) (guard : d259601 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31651 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259600 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31666 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31668 (p : Pattern) (guard : d259602 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259591 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31657 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31669 (p : Pattern) (guard : d259603 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259601 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31667 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259602 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31668 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31670 (p : Pattern) (guard : d259604 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259593 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31659 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259603 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31669 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31671 (p : Pattern) (guard : d259605 p = 1) : d47686 p ≤ (-2 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259604 p = 1 := by simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31670 p hg
    simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31672 (p : Pattern) (guard : d259606 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259605 p = 1 := by simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31671 p hg
    simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31673 (p : Pattern) (guard : d259607 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259600 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31666 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31674 (p : Pattern) (guard : d259608 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259607 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31673 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31675 (p : Pattern) (guard : d259609 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259603 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31669 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259608 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31674 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31676 (p : Pattern) (guard : d259610 p = 1) : d47686 p ≤ (-2 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259609 p = 1 := by simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31675 p hg
    simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31677 (p : Pattern) (guard : d259611 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259610 p = 1 := by simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31676 p hg
    simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31678 (p : Pattern) (guard : d259612 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259606 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31672 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259611 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31677 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31679 (p : Pattern) (guard : d259613 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259611 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31677 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31680 (p : Pattern) (guard : d259614 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259612 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31678 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259613 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31679 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31681 (p : Pattern) (guard : d259615 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259614 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31680 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31682 (p : Pattern) (guard : d259616 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259615 p = 1 := by simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31681 p hg
    simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31683 (p : Pattern) (guard : d259617 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259616 p = 1 := by simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31682 p hg
    simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31684 (p : Pattern) (guard : d259618 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259613 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31679 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31685 (p : Pattern) (guard : d259619 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259618 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31684 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31686 (p : Pattern) (guard : d259620 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259619 p = 1 := by simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31685 p hg
    simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31687 (p : Pattern) (guard : d259621 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259620 p = 1 := by simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31686 p hg
    simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31688 (p : Pattern) (guard : d259622 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259617 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31683 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259621 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31689 (p : Pattern) (guard : d259623 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259622 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31688 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31690 (p : Pattern) (guard : d259624 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259623 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31689 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31691 (p : Pattern) (guard : d259625 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259624 p = 1 := by simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31690 p hg
    simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31692 (p : Pattern) (guard : d259626 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259621 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31693 (p : Pattern) (guard : d259627 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259626 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31692 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31694 (p : Pattern) (guard : d259628 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259627 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31693 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31695 (p : Pattern) (guard : d259629 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259628 p = 1 := by simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31694 p hg
    simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31696 (p : Pattern) (guard : d259630 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259625 p = 1 := by simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31691 p hg
    simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259629 p = 1 := by simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31695 p hg
    simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31697 (p : Pattern) (guard : d259631 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259630 p = 1 := by simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31696 p hg
    simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31698 (p : Pattern) (guard : d259632 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259631 p = 1 := by simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31697 p hg
    simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31699 (p : Pattern) (guard : d259633 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259632 p = 1 := by simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31698 p hg
    simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31700 (p : Pattern) (guard : d259634 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259633 p = 1 := by simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31699 p hg
    simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31701 (p : Pattern) (guard : d259635 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259634 p = 1 := by simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31700 p hg
    simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31702 (p : Pattern) (guard : d259638 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259624 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31690 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31703 (p : Pattern) (guard : d259639 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259628 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31694 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31704 (p : Pattern) (guard : d259640 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259638 p = 1 := by simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31702 p hg
    simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259639 p = 1 := by simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31703 p hg
    simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31705 (p : Pattern) (guard : d259641 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259640 p = 1 := by simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31704 p hg
    simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31706 (p : Pattern) (guard : d259642 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259641 p = 1 := by simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31705 p hg
    simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31707 (p : Pattern) (guard : d259643 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259642 p = 1 := by simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31706 p hg
    simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31708 (p : Pattern) (guard : d259644 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259643 p = 1 := by simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31707 p hg
    simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31709 (p : Pattern) (guard : d259645 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259634 p = 1 := by simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31700 p hg
    simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259644 p = 1 := by simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31708 p hg
    simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31710 (p : Pattern) (guard : d259646 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259635 p = 1 := by simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31701 p hg
    simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259645 p = 1 := by simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31709 p hg
    simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31711 (p : Pattern) (guard : d259647 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259646 p = 1 := by simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31710 p hg
    simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31712 (p : Pattern) (guard : d260191 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259647 p = 1 := by simpa only [d260191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31711 p hg
    simpa only [d260191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31713 (p : Pattern) (guard : d260192 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260191 p = 1 := by simpa only [d260192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31712 p hg
    simpa only [d260192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31714 (p : Pattern) (guard : d258183 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31413 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31715 (p : Pattern) (guard : d258184 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31714 p hg
    simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31716 (p : Pattern) (guard : d258185 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30850 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31715 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31717 (p : Pattern) (guard : d258186 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31716 p hg
    simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31718 (p : Pattern) (guard : d258187 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258186 p = 1 := by simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31717 p hg
    simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31719 (p : Pattern) (guard : d258188 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258187 p = 1 := by simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31718 p hg
    simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31720 (p : Pattern) (guard : d258189 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258188 p = 1 := by simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31719 p hg
    simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31721 (p : Pattern) (guard : d259573 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31015 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31722 (p : Pattern) (guard : d259574 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31721 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31723 (p : Pattern) (guard : d259575 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31416 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31722 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31724 (p : Pattern) (guard : d259576 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30843 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31725 (p : Pattern) (guard : d259577 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31723 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31724 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31726 (p : Pattern) (guard : d259578 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31725 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31727 (p : Pattern) (guard : d259579 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31726 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31728 (p : Pattern) (guard : d259580 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31727 p hg
    simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d259580, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31729 (p : Pattern) (guard : d259581 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31715 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31728 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31730 (p : Pattern) (guard : d259582 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31729 p hg
    simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259582, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31731 (p : Pattern) (guard : d259583 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259582 p = 1 := by simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31730 p hg
    simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259583, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31732 (p : Pattern) (guard : d259584 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259583 p = 1 := by simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31731 p hg
    simpa only [d259584, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31733 (p : Pattern) (guard : d259585 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259584 p = 1 := by simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31732 p hg
    simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d259585, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31734 (p : Pattern) (guard : d259586 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258189 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31720 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259585 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31733 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31735 (p : Pattern) (guard : d259587 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31728 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30850 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31736 (p : Pattern) (guard : d259588 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31735 p hg
    simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259588, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31737 (p : Pattern) (guard : d259589 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259588 p = 1 := by simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31736 p hg
    simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259589, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31738 (p : Pattern) (guard : d259590 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259589 p = 1 := by simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31737 p hg
    simpa only [d259590, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31739 (p : Pattern) (guard : d259591 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259590 p = 1 := by simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31738 p hg
    simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d259591, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31740 (p : Pattern) (guard : d259592 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31733 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259591 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31739 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31741 (p : Pattern) (guard : d259593 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259586 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31734 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259592 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31740 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31742 (p : Pattern) (guard : d259594 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31726 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31433 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31743 (p : Pattern) (guard : d259595 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31742 p hg
    simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d259595, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31744 (p : Pattern) (guard : d259596 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31743 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30850 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31745 (p : Pattern) (guard : d259597 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31744 p hg
    simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259597, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31746 (p : Pattern) (guard : d259598 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259597 p = 1 := by simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31745 p hg
    simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259598, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31747 (p : Pattern) (guard : d259599 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259598 p = 1 := by simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31746 p hg
    simpa only [d259599, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31748 (p : Pattern) (guard : d259600 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259599 p = 1 := by simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31747 p hg
    simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d259600, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31749 (p : Pattern) (guard : d259601 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31733 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259600 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31748 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
