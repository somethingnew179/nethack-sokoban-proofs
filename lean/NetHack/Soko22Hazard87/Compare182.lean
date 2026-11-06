import NetHack.Soko22Hazard87.Compare181
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45500 (p : Pattern) (guard : d342826 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45501 (p : Pattern) (guard : d342827 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342826 p = 1 := by simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45500 p hg
    simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45502 (p : Pattern) (guard : d342828 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342827 p = 1 := by simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45501 p hg
    simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45503 (p : Pattern) (guard : d342829 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342828 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45502 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45347 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45504 (p : Pattern) (guard : d342830 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342829 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45503 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342718 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45349 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45505 (p : Pattern) (guard : d342831 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342830 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45504 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342719 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45350 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45506 (p : Pattern) (guard : d342832 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342831 p = 1 := by simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45505 p hg
    simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45507 (p : Pattern) (guard : d342833 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342832 p = 1 := by simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45506 p hg
    simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45508 (p : Pattern) (guard : d342834 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45507 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342722 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45353 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45509 (p : Pattern) (guard : d342835 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342834 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45508 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342723 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45355 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45510 (p : Pattern) (guard : d342836 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342835 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45509 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45511 (p : Pattern) (guard : d342837 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342836 p = 1 := by simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45510 p hg
    simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45512 (p : Pattern) (guard : d342838 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342837 p = 1 := by simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45511 p hg
    simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45513 (p : Pattern) (guard : d342839 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45512 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342727 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45360 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45514 (p : Pattern) (guard : d342840 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342839 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45513 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45515 (p : Pattern) (guard : d342841 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342840 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45514 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45516 (p : Pattern) (guard : d342858 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342841 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45515 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45517 (p : Pattern) (guard : d342859 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342858 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45516 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342738 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45364 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45518 (p : Pattern) (guard : d342922 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342859 p = 1 := by simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45517 p hg
    simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45519 (p : Pattern) (guard : d342923 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342922 p = 1 := by simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45518 p hg
    simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45520 (p : Pattern) (guard : d342924 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342923 p = 1 := by simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45519 p hg
    simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45521 (p : Pattern) (guard : d342925 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342924 p = 1 := by simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45520 p hg
    simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45522 (p : Pattern) (guard : d343985 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343985, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343985, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342925 p = 1 := by simpa only [d343985, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45521 p hg
    simpa only [d343985, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45523 (p : Pattern) (guard : d343986 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343985 p = 1 := by simpa only [d343986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45522 p hg
    simpa only [d343986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45524 (p : Pattern) (guard : d343987 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d343986 p = 1 := by simpa only [d343987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45523 p hg
    simpa only [d343987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45525 (p : Pattern) (guard : d343988 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d343987 p = 1 := by simpa only [d343988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45524 p hg
    simpa only [d343988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45526 (p : Pattern) (guard : d343989 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d343988 p = 1 := by simpa only [d343989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45525 p hg
    simpa only [d343989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45527 (p : Pattern) (guard : d343990 p = 1) : d51470 p ≤ (7 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d343984 p = 1 := by simpa only [d343990, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45499 p hg
    simpa only [d343990, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343989 p = 1 := by simpa only [d343990, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45526 p hg
    simpa only [d343990, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45528 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (7 : Int) + d2 p := by
  omega
theorem compare45529 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45528 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45383 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45530 (p : Pattern) (guard : d1523 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45529 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45531 (p : Pattern) (guard : d1524 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45530 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45385 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45532 (p : Pattern) (guard : d342817 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45531 p hg
    simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1085 p = 1 := by simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45386 p hg
    simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45533 (p : Pattern) (guard : d342818 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d342817 p = 1 := by simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45532 p hg
    simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45387 p hg
    simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45534 (p : Pattern) (guard : d342819 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d342818 p = 1 := by simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45533 p hg
    simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45535 (p : Pattern) (guard : d342820 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d342819 p = 1 := by simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45534 p hg
    simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45536 (p : Pattern) (guard : d342821 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d342820 p = 1 := by simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45535 p hg
    simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45391 p hg
    simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45537 (p : Pattern) (guard : d342822 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342821 p = 1 := by simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45536 p hg
    simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342710 p = 1 := by simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45393 p hg
    simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45538 (p : Pattern) (guard : d342823 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342822 p = 1 := by simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45537 p hg
    simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45539 (p : Pattern) (guard : d342824 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342823 p = 1 := by simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45538 p hg
    simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342712 p = 1 := by simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45396 p hg
    simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45540 (p : Pattern) (guard : d342879 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342824 p = 1 := by simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45539 p hg
    simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45541 (p : Pattern) (guard : d342825 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d342824 p = 1 := by simpa only [d342825, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45454 p hg
    simpa only [d342825, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342825, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d342825, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45542 (p : Pattern) (guard : d342880 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d342879 p = 1 := by simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45540 p hg
    simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342825 p = 1 := by simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45541 p hg
    simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45543 (p : Pattern) (guard : d342826 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45544 (p : Pattern) (guard : d342881 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d342880 p = 1 := by simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45542 p hg
    simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342826 p = 1 := by simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45543 p hg
    simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45545 (p : Pattern) (guard : d342882 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342881 p = 1 := by simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45544 p hg
    simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45546 (p : Pattern) (guard : d342883 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342882 p = 1 := by simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45545 p hg
    simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342758 p = 1 := by simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45406 p hg
    simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45547 (p : Pattern) (guard : d342884 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342883 p = 1 := by simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45546 p hg
    simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342759 p = 1 := by simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45408 p hg
    simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45548 (p : Pattern) (guard : d342885 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342884 p = 1 := by simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45547 p hg
    simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342760 p = 1 := by simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45409 p hg
    simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45549 (p : Pattern) (guard : d342886 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342885 p = 1 := by simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45548 p hg
    simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45550 (p : Pattern) (guard : d342887 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342886 p = 1 := by simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45549 p hg
    simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45551 (p : Pattern) (guard : d342888 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342887 p = 1 := by simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45550 p hg
    simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342763 p = 1 := by simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45412 p hg
    simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45552 (p : Pattern) (guard : d342889 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342888 p = 1 := by simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45551 p hg
    simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342764 p = 1 := by simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45414 p hg
    simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45553 (p : Pattern) (guard : d342890 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342889 p = 1 := by simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45552 p hg
    simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45554 (p : Pattern) (guard : d342891 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342890 p = 1 := by simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45553 p hg
    simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45555 (p : Pattern) (guard : d342892 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342891 p = 1 := by simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45554 p hg
    simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45556 (p : Pattern) (guard : d342893 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342892 p = 1 := by simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45555 p hg
    simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342768 p = 1 := by simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45419 p hg
    simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45557 (p : Pattern) (guard : d342894 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342893 p = 1 := by simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45556 p hg
    simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45558 (p : Pattern) (guard : d342895 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342894 p = 1 := by simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45557 p hg
    simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45559 (p : Pattern) (guard : d342896 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342895 p = 1 := by simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45558 p hg
    simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45560 (p : Pattern) (guard : d342897 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342896 p = 1 := by simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45559 p hg
    simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342772 p = 1 := by simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45423 p hg
    simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45561 (p : Pattern) (guard : d343991 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342897 p = 1 := by simpa only [d343991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45560 p hg
    simpa only [d343991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45562 (p : Pattern) (guard : d343992 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343991 p = 1 := by simpa only [d343992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45561 p hg
    simpa only [d343992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45563 (p : Pattern) (guard : d343993 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343992 p = 1 := by simpa only [d343993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45562 p hg
    simpa only [d343993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45564 (p : Pattern) (guard : d343994 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343993 p = 1 := by simpa only [d343994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45563 p hg
    simpa only [d343994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45565 (p : Pattern) (guard : d343995 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343995, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343995, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343994 p = 1 := by simpa only [d343995, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45564 p hg
    simpa only [d343995, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45566 (p : Pattern) (guard : d343996 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343995 p = 1 := by simpa only [d343996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45565 p hg
    simpa only [d343996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45567 (p : Pattern) (guard : d343997 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d343996 p = 1 := by simpa only [d343997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45566 p hg
    simpa only [d343997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45568 (p : Pattern) (guard : d343998 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d343997 p = 1 := by simpa only [d343998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45567 p hg
    simpa only [d343998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45569 (p : Pattern) (guard : d343999 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d343998 p = 1 := by simpa only [d343999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45568 p hg
    simpa only [d343999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45570 (p : Pattern) (guard : d344000 p = 1) : d51634 p ≤ (7 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d343999 p = 1 := by simpa only [d344000, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45569 p hg
    simpa only [d344000, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d344000, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d344000, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45571 (p : Pattern) (guard : d344001 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d343990 p = 1 := by simpa only [d344001, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45527 p hg
    simpa only [d344001, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344000 p = 1 := by simpa only [d344001, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45570 p hg
    simpa only [d344001, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45572 (p : Pattern) (guard : d344002 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d344002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d344002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344001 p = 1 := by simpa only [d344002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45571 p hg
    simpa only [d344002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45573 (p : Pattern) (guard : d344003 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d344003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d344003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344002 p = 1 := by simpa only [d344003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45572 p hg
    simpa only [d344003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45574 (p : Pattern) (guard : d344004 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d344004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d344004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344003 p = 1 := by simpa only [d344004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45573 p hg
    simpa only [d344004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45575 (p : Pattern) (guard : d344005 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d344005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d344005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344004 p = 1 := by simpa only [d344005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45574 p hg
    simpa only [d344005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45576 (p : Pattern) (guard : d344006 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d344006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d344006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344005 p = 1 := by simpa only [d344006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45575 p hg
    simpa only [d344006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45577 (p : Pattern) (guard : d344007 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d344007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d344007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344006 p = 1 := by simpa only [d344007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45576 p hg
    simpa only [d344007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45578 (p : Pattern) (guard : d344008 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d343982 p = 1 := by simpa only [d344008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45442 p hg
    simpa only [d344008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d344007 p = 1 := by simpa only [d344008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45577 p hg
    simpa only [d344008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45579 (p : Pattern) (guard : d2001 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45445 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45580 (p : Pattern) (guard : d2002 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45579 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45581 (p : Pattern) (guard : d2005 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45445 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45582 (p : Pattern) (guard : d42940 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45581 p hg
    simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1085 p = 1 := by simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45273 p hg
    simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45583 (p : Pattern) (guard : d42941 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45580 p hg
    simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42940 p = 1 := by simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45582 p hg
    simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45584 (p : Pattern) (guard : d42942 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d42941 p = 1 := by simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45583 p hg
    simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45585 (p : Pattern) (guard : d42943 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d42942 p = 1 := by simpa only [d42943, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45584 p hg
    simpa only [d42943, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d42943, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d42943, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45586 (p : Pattern) (guard : d366224 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d42943 p = 1 := by simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45585 p hg
    simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342820 p = 1 := by simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45450 p hg
    simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45587 (p : Pattern) (guard : d366225 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366224 p = 1 := by simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45586 p hg
    simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342821 p = 1 := by simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45451 p hg
    simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45588 (p : Pattern) (guard : d366226 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366225 p = 1 := by simpa only [d366226, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45587 p hg
    simpa only [d366226, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366226, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366226, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45589 (p : Pattern) (guard : d366227 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366226 p = 1 := by simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45588 p hg
    simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342823 p = 1 := by simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45453 p hg
    simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45590 (p : Pattern) (guard : d366228 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366227 p = 1 := by simpa only [d366228, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45589 p hg
    simpa only [d366228, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366228, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366228, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45591 (p : Pattern) (guard : d366229 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366228 p = 1 := by simpa only [d366229, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45590 p hg
    simpa only [d366229, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366229, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366229, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45592 (p : Pattern) (guard : d366230 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366229 p = 1 := by simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45591 p hg
    simpa only [d366230, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45593 (p : Pattern) (guard : d366231 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366230 p = 1 := by simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45592 p hg
    simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366231, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45594 (p : Pattern) (guard : d366232 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366231 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45593 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342828 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45458 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45595 (p : Pattern) (guard : d342959 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342821 p = 1 := by simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45451 p hg
    simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45596 (p : Pattern) (guard : d342960 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342959 p = 1 := by simpa only [d342960, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45595 p hg
    simpa only [d342960, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342960, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d342960, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45597 (p : Pattern) (guard : d342961 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342960 p = 1 := by simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45596 p hg
    simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342712 p = 1 := by simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45283 p hg
    simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45598 (p : Pattern) (guard : d342962 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d342961 p = 1 := by simpa only [d342962, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45597 p hg
    simpa only [d342962, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342962, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d342962, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45599 (p : Pattern) (guard : d342963 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d342962 p = 1 := by simpa only [d342963, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45598 p hg
    simpa only [d342963, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342963, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d342963, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45600 (p : Pattern) (guard : d342964 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342963 p = 1 := by simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45599 p hg
    simpa only [d342964, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45601 (p : Pattern) (guard : d342965 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342964 p = 1 := by simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45600 p hg
    simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d342965, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45602 (p : Pattern) (guard : d342966 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342965 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45601 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45292 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45603 (p : Pattern) (guard : d366233 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366232 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45594 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342966 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45602 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45604 (p : Pattern) (guard : d366234 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366233 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45603 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342830 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45460 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45605 (p : Pattern) (guard : d366235 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366234 p = 1 := by simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45604 p hg
    simpa only [d366235, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45606 (p : Pattern) (guard : d366236 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366235 p = 1 := by simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45605 p hg
    simpa only [d366236, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45607 (p : Pattern) (guard : d366237 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366236 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45606 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342833 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45463 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45608 (p : Pattern) (guard : d343081 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45463 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45609 (p : Pattern) (guard : d366308 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366237 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45607 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343081 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45608 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45610 (p : Pattern) (guard : d366309 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366308 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45609 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45611 (p : Pattern) (guard : d366310 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366309 p = 1 := by simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45610 p hg
    simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d366310, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45612 (p : Pattern) (guard : d366311 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366310 p = 1 := by simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45611 p hg
    simpa only [d366311, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45613 (p : Pattern) (guard : d343086 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d343081 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45608 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45614 (p : Pattern) (guard : d343087 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d343086 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45613 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45615 (p : Pattern) (guard : d343088 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d343087 p = 1 := by simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45614 p hg
    simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d343088, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45616 (p : Pattern) (guard : d343089 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343088 p = 1 := by simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45615 p hg
    simpa only [d343089, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45617 (p : Pattern) (guard : d366312 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45612 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343089 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45616 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45618 (p : Pattern) (guard : d366313 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366312 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45617 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45619 (p : Pattern) (guard : d366314 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366313 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45618 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45620 (p : Pattern) (guard : d366315 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366314 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45619 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45621 (p : Pattern) (guard : d343094 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343089 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45616 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45622 (p : Pattern) (guard : d343095 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343094 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45621 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45623 (p : Pattern) (guard : d343096 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343095 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45622 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45624 (p : Pattern) (guard : d343097 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343096 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45623 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45625 (p : Pattern) (guard : d366316 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366315 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45620 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343097 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45624 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45626 (p : Pattern) (guard : d366317 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366316 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45625 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45627 (p : Pattern) (guard : d366318 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366317 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45626 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45628 (p : Pattern) (guard : d366319 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366318 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45627 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45629 (p : Pattern) (guard : d366320 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366319 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45628 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45630 (p : Pattern) (guard : d366321 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366320 p = 1 := by simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45629 p hg
    simpa only [d366321, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45631 (p : Pattern) (guard : d366311 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366310 p = 1 := by simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45611 p hg
    simpa only [d366311, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45632 (p : Pattern) (guard : d343089 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343088 p = 1 := by simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45615 p hg
    simpa only [d343089, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45633 (p : Pattern) (guard : d366312 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45631 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343089 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45632 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45634 (p : Pattern) (guard : d366313 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366312 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45633 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45635 (p : Pattern) (guard : d366314 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366313 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45634 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45636 (p : Pattern) (guard : d366315 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366314 p = 1 := by simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45635 p hg
    simpa only [d366315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45637 (p : Pattern) (guard : d343094 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343089 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45632 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45638 (p : Pattern) (guard : d343095 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343094 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45637 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45639 (p : Pattern) (guard : d343096 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343095 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45638 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45640 (p : Pattern) (guard : d343097 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343096 p = 1 := by simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45639 p hg
    simpa only [d343097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45641 (p : Pattern) (guard : d366316 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366315 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45636 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343097 p = 1 := by simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45640 p hg
    simpa only [d366316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45642 (p : Pattern) (guard : d366317 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366316 p = 1 := by simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45641 p hg
    simpa only [d366317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45643 (p : Pattern) (guard : d366318 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366317 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45642 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45644 (p : Pattern) (guard : d366319 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366318 p = 1 := by simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45643 p hg
    simpa only [d366319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45645 (p : Pattern) (guard : d366320 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366319 p = 1 := by simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45644 p hg
    simpa only [d366320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45646 (p : Pattern) (guard : d366324 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366314 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45619 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45647 (p : Pattern) (guard : d343107 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343096 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45623 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45648 (p : Pattern) (guard : d366325 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366324 p = 1 := by simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45646 p hg
    simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343107 p = 1 := by simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45647 p hg
    simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45649 (p : Pattern) (guard : d366326 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366325 p = 1 := by simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45648 p hg
    simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45650 (p : Pattern) (guard : d366327 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366326 p = 1 := by simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45649 p hg
    simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45651 (p : Pattern) (guard : d366328 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366327 p = 1 := by simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45650 p hg
    simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45652 (p : Pattern) (guard : d366329 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366328 p = 1 := by simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45651 p hg
    simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45653 (p : Pattern) (guard : d366330 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366320 p = 1 := by simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45645 p hg
    simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366329 p = 1 := by simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45652 p hg
    simpa only [d366330, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45654 (p : Pattern) (guard : d366331 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366321 p = 1 := by simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45630 p hg
    simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366330 p = 1 := by simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45653 p hg
    simpa only [d366331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45655 (p : Pattern) (guard : d366332 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366331 p = 1 := by simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45654 p hg
    simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d366332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45656 (p : Pattern) (guard : d367439 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366332 p = 1 := by simpa only [d367439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45655 p hg
    simpa only [d367439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45657 (p : Pattern) (guard : d367440 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367439 p = 1 := by simpa only [d367440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45656 p hg
    simpa only [d367440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45658 (p : Pattern) (guard : d366229 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45659 (p : Pattern) (guard : d366230 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366229 p = 1 := by simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45658 p hg
    simpa only [d366230, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45660 (p : Pattern) (guard : d366231 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366230 p = 1 := by simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45659 p hg
    simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366231, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45661 (p : Pattern) (guard : d366232 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366231 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45660 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342828 p = 1 := by simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45502 p hg
    simpa only [d366232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45662 (p : Pattern) (guard : d342963 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45663 (p : Pattern) (guard : d342964 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342963 p = 1 := by simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45662 p hg
    simpa only [d342964, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45664 (p : Pattern) (guard : d342965 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342964 p = 1 := by simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45663 p hg
    simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d342965, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45665 (p : Pattern) (guard : d342966 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342965 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45664 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45347 p hg
    simpa only [d342966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45666 (p : Pattern) (guard : d366233 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366232 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45661 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342966 p = 1 := by simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45665 p hg
    simpa only [d366233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45667 (p : Pattern) (guard : d366234 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366233 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45666 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342830 p = 1 := by simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45504 p hg
    simpa only [d366234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45668 (p : Pattern) (guard : d366235 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366234 p = 1 := by simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45667 p hg
    simpa only [d366235, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45669 (p : Pattern) (guard : d366236 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366235 p = 1 := by simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45668 p hg
    simpa only [d366236, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45670 (p : Pattern) (guard : d366237 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366236 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45669 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342833 p = 1 := by simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45507 p hg
    simpa only [d366237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45671 (p : Pattern) (guard : d343081 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45507 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d343081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45672 (p : Pattern) (guard : d366308 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366237 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45670 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343081 p = 1 := by simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45671 p hg
    simpa only [d366308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45673 (p : Pattern) (guard : d366309 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366308 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45672 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45674 (p : Pattern) (guard : d366310 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366309 p = 1 := by simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45673 p hg
    simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d366310, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45675 (p : Pattern) (guard : d366311 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366310 p = 1 := by simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45674 p hg
    simpa only [d366311, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45676 (p : Pattern) (guard : d343086 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d343081 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45671 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d343086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45677 (p : Pattern) (guard : d343087 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d343086 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45676 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d343087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45678 (p : Pattern) (guard : d343088 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d343087 p = 1 := by simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45677 p hg
    simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d343088, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45679 (p : Pattern) (guard : d343089 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343088 p = 1 := by simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45678 p hg
    simpa only [d343089, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45680 (p : Pattern) (guard : d366312 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366311 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45675 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343089 p = 1 := by simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45679 p hg
    simpa only [d366312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45681 (p : Pattern) (guard : d366313 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366312 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45680 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45682 (p : Pattern) (guard : d366314 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366313 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45681 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45683 (p : Pattern) (guard : d366324 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366314 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45682 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45684 (p : Pattern) (guard : d343094 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343089 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45679 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d343094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45685 (p : Pattern) (guard : d343095 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343094 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45684 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d343095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45686 (p : Pattern) (guard : d343096 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343095 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45685 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d343096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45687 (p : Pattern) (guard : d343107 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343096 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45686 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d343107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45688 (p : Pattern) (guard : d366325 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366324 p = 1 := by simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45683 p hg
    simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343107 p = 1 := by simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45687 p hg
    simpa only [d366325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45689 (p : Pattern) (guard : d366326 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366325 p = 1 := by simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45688 p hg
    simpa only [d366326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45690 (p : Pattern) (guard : d366327 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366326 p = 1 := by simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45689 p hg
    simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45691 (p : Pattern) (guard : d366328 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366327 p = 1 := by simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45690 p hg
    simpa only [d366328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45692 (p : Pattern) (guard : d366329 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366328 p = 1 := by simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45691 p hg
    simpa only [d366329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45693 (p : Pattern) (guard : d367441 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367441, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367441, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366329 p = 1 := by simpa only [d367441, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45692 p hg
    simpa only [d367441, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45694 (p : Pattern) (guard : d367442 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367441 p = 1 := by simpa only [d367442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45693 p hg
    simpa only [d367442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45695 (p : Pattern) (guard : d367443 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367442 p = 1 := by simpa only [d367443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45694 p hg
    simpa only [d367443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45696 (p : Pattern) (guard : d367444 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367443 p = 1 := by simpa only [d367444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45695 p hg
    simpa only [d367444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45697 (p : Pattern) (guard : d367445 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367444 p = 1 := by simpa only [d367445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45696 p hg
    simpa only [d367445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45698 (p : Pattern) (guard : d367446 p = 1) : d51470 p ≤ (7 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367440 p = 1 := by simpa only [d367446, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45657 p hg
    simpa only [d367446, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367445 p = 1 := by simpa only [d367446, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45697 p hg
    simpa only [d367446, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45699 (p : Pattern) (guard : d2001 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45530 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45700 (p : Pattern) (guard : d2002 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45699 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45701 (p : Pattern) (guard : d2005 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45530 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45702 (p : Pattern) (guard : d42940 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45701 p hg
    simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1085 p = 1 := by simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45386 p hg
    simpa only [d42940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45703 (p : Pattern) (guard : d42941 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45700 p hg
    simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42940 p = 1 := by simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45702 p hg
    simpa only [d42941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45704 (p : Pattern) (guard : d42942 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d42941 p = 1 := by simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45703 p hg
    simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d42942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45705 (p : Pattern) (guard : d42943 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d42942 p = 1 := by simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45704 p hg
    simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d42943, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45706 (p : Pattern) (guard : d366224 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d42943 p = 1 := by simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45705 p hg
    simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342820 p = 1 := by simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45535 p hg
    simpa only [d366224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45707 (p : Pattern) (guard : d366225 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366224 p = 1 := by simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45706 p hg
    simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342821 p = 1 := by simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45536 p hg
    simpa only [d366225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45708 (p : Pattern) (guard : d366226 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366225 p = 1 := by simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45707 p hg
    simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366226, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45709 (p : Pattern) (guard : d366227 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366226 p = 1 := by simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45708 p hg
    simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342823 p = 1 := by simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45538 p hg
    simpa only [d366227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45710 (p : Pattern) (guard : d366271 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366227 p = 1 := by simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45709 p hg
    simpa only [d366271, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45711 (p : Pattern) (guard : d366228 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366227 p = 1 := by simpa only [d366228, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45589 p hg
    simpa only [d366228, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366228, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366228, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45712 (p : Pattern) (guard : d366272 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366271 p = 1 := by simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45710 p hg
    simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366228 p = 1 := by simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45711 p hg
    simpa only [d366272, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45713 (p : Pattern) (guard : d366229 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45714 (p : Pattern) (guard : d366273 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366272 p = 1 := by simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45712 p hg
    simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366229 p = 1 := by simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45713 p hg
    simpa only [d366273, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45715 (p : Pattern) (guard : d366274 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366273 p = 1 := by simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45714 p hg
    simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d366274, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45716 (p : Pattern) (guard : d366275 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366274 p = 1 := by simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45715 p hg
    simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342882 p = 1 := by simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45545 p hg
    simpa only [d366275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45717 (p : Pattern) (guard : d342959 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342821 p = 1 := by simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45536 p hg
    simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d342959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45718 (p : Pattern) (guard : d342960 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342959 p = 1 := by simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45717 p hg
    simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d342960, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45719 (p : Pattern) (guard : d342961 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342960 p = 1 := by simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45718 p hg
    simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342712 p = 1 := by simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45396 p hg
    simpa only [d342961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45720 (p : Pattern) (guard : d343032 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342961 p = 1 := by simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45719 p hg
    simpa only [d343032, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45721 (p : Pattern) (guard : d342962 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d342961 p = 1 := by simpa only [d342962, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45597 p hg
    simpa only [d342962, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342962, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d342962, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45722 (p : Pattern) (guard : d343033 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d343032 p = 1 := by simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45720 p hg
    simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342962 p = 1 := by simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45721 p hg
    simpa only [d343033, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45723 (p : Pattern) (guard : d342963 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45724 (p : Pattern) (guard : d343034 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d343033 p = 1 := by simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45722 p hg
    simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342963 p = 1 := by simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45723 p hg
    simpa only [d343034, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45725 (p : Pattern) (guard : d343035 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d343034 p = 1 := by simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45724 p hg
    simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d343035, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45726 (p : Pattern) (guard : d343036 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d343035 p = 1 := by simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45725 p hg
    simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342758 p = 1 := by simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45406 p hg
    simpa only [d343036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45727 (p : Pattern) (guard : d366276 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366275 p = 1 := by simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45716 p hg
    simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343036 p = 1 := by simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45726 p hg
    simpa only [d366276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45728 (p : Pattern) (guard : d366277 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366276 p = 1 := by simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45727 p hg
    simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342884 p = 1 := by simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45547 p hg
    simpa only [d366277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45729 (p : Pattern) (guard : d366278 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366277 p = 1 := by simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45728 p hg
    simpa only [d366278, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45730 (p : Pattern) (guard : d366279 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366278 p = 1 := by simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45729 p hg
    simpa only [d366279, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45731 (p : Pattern) (guard : d366280 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366279 p = 1 := by simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45730 p hg
    simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342887 p = 1 := by simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45550 p hg
    simpa only [d366280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45732 (p : Pattern) (guard : d343274 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342887 p = 1 := by simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45550 p hg
    simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45733 (p : Pattern) (guard : d366468 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366280 p = 1 := by simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45731 p hg
    simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343274 p = 1 := by simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45732 p hg
    simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45734 (p : Pattern) (guard : d366469 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366468 p = 1 := by simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45733 p hg
    simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45735 (p : Pattern) (guard : d366470 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366469 p = 1 := by simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45734 p hg
    simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45736 (p : Pattern) (guard : d366471 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366470 p = 1 := by simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45735 p hg
    simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45737 (p : Pattern) (guard : d343283 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d343274 p = 1 := by simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45732 p hg
    simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45738 (p : Pattern) (guard : d343284 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d343283 p = 1 := by simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45737 p hg
    simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45739 (p : Pattern) (guard : d343285 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d343284 p = 1 := by simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45738 p hg
    simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45740 (p : Pattern) (guard : d343286 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343285 p = 1 := by simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45739 p hg
    simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45741 (p : Pattern) (guard : d366476 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366471 p = 1 := by simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45736 p hg
    simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343286 p = 1 := by simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45740 p hg
    simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45742 (p : Pattern) (guard : d366477 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366476 p = 1 := by simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45741 p hg
    simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45743 (p : Pattern) (guard : d366478 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366477 p = 1 := by simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45742 p hg
    simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45744 (p : Pattern) (guard : d366479 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366478 p = 1 := by simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45743 p hg
    simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45745 (p : Pattern) (guard : d343304 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343286 p = 1 := by simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45740 p hg
    simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45746 (p : Pattern) (guard : d343305 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343304 p = 1 := by simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45745 p hg
    simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45747 (p : Pattern) (guard : d343306 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343305 p = 1 := by simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45746 p hg
    simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45748 (p : Pattern) (guard : d343307 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343306 p = 1 := by simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45747 p hg
    simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45749 (p : Pattern) (guard : d367447 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366479 p = 1 := by simpa only [d367447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45744 p hg
    simpa only [d367447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343307 p = 1 := by simpa only [d367447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45748 p hg
    simpa only [d367447, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
