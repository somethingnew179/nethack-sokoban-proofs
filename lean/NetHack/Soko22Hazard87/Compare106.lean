import NetHack.Soko22Hazard87.Compare105
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26500 (p : Pattern) (guard : d1529 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26498 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26499 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26501 (p : Pattern) (guard : d1530 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26500 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26502 (p : Pattern) (guard : d1532 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26491 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25906 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26503 (p : Pattern) (guard : d1533 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25891 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26502 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26504 (p : Pattern) (guard : d1534 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26503 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26505 (p : Pattern) (guard : d1535 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26504 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26506 (p : Pattern) (guard : d1536 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26095 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26505 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26507 (p : Pattern) (guard : d1537 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26501 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26506 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26508 (p : Pattern) (guard : d1538 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26507 p hg
    simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1538, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26509 (p : Pattern) (guard : d1664 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1663 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26490 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1538 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26508 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26510 (p : Pattern) (guard : d1665 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26509 p hg
    simpa only [d1665, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1665, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26511 (p : Pattern) (guard : d1666 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1665 p = 1 := by simpa only [d1666, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26510 p hg
    simpa only [d1666, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1666, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1666, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26512 (p : Pattern) (guard : d1667 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1667, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1667, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1666 p = 1 := by simpa only [d1667, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26511 p hg
    simpa only [d1667, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26513 (p : Pattern) (guard : d1668 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26512 p hg
    simpa only [d1668, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1668, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26514 (p : Pattern) (guard : d10035 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26508 p hg
    simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26515 (p : Pattern) (guard : d10036 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10035 p = 1 := by simpa only [d10036, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26514 p hg
    simpa only [d10036, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10036, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10036, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26516 (p : Pattern) (guard : d10038 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10036 p = 1 := by simpa only [d10038, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26515 p hg
    simpa only [d10038, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10038, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10038, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26517 (p : Pattern) (guard : d16859 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16859, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d16859, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10038 p = 1 := by simpa only [d16859, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26516 p hg
    simpa only [d16859, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26518 (p : Pattern) (guard : d16860 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16859 p = 1 := by simpa only [d16860, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26517 p hg
    simpa only [d16860, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16860, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d16860, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26519 (p : Pattern) (guard : d16861 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26513 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16860 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26518 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26520 (p : Pattern) (guard : d10042 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26521 (p : Pattern) (guard : d10043 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10042 p = 1 := by simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26520 p hg
    simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26522 (p : Pattern) (guard : d10044 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10043 p = 1 := by simpa only [d10044, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26521 p hg
    simpa only [d10044, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10044, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10044, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26523 (p : Pattern) (guard : d10045 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10044 p = 1 := by simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26522 p hg
    simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26524 (p : Pattern) (guard : d10046 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10045 p = 1 := by simpa only [d10046, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26523 p hg
    simpa only [d10046, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10046, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10046, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26525 (p : Pattern) (guard : d10048 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10046 p = 1 := by simpa only [d10048, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26524 p hg
    simpa only [d10048, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10048, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10048, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26526 (p : Pattern) (guard : d15229 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15229, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d15229, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10048 p = 1 := by simpa only [d15229, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26525 p hg
    simpa only [d15229, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26527 (p : Pattern) (guard : d15230 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15229 p = 1 := by simpa only [d15230, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26526 p hg
    simpa only [d15230, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15230, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d15230, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26528 (p : Pattern) (guard : d10051 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26500 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26529 (p : Pattern) (guard : d10052 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10051 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26528 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26530 (p : Pattern) (guard : d10053 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10052 p = 1 := by simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26529 p hg
    simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10053, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26531 (p : Pattern) (guard : d2005 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26494 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26532 (p : Pattern) (guard : d2006 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26531 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26533 (p : Pattern) (guard : d10054 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26532 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26534 (p : Pattern) (guard : d10055 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26533 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26535 (p : Pattern) (guard : d10056 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10055 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26534 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26536 (p : Pattern) (guard : d1547 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25906 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26537 (p : Pattern) (guard : d5122 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25903 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26536 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26538 (p : Pattern) (guard : d10057 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26537 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26539 (p : Pattern) (guard : d10058 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26538 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26540 (p : Pattern) (guard : d10059 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10056 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26535 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26539 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26541 (p : Pattern) (guard : d10060 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10059 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26540 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26542 (p : Pattern) (guard : d10061 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10060 p = 1 := by simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26541 p hg
    simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10061, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26543 (p : Pattern) (guard : d10062 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10053 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26530 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26542 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26544 (p : Pattern) (guard : d10063 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26543 p hg
    simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10063, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26545 (p : Pattern) (guard : d10065 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26544 p hg
    simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10065, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26546 (p : Pattern) (guard : d15151 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26545 p hg
    simpa only [d15151, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26547 (p : Pattern) (guard : d15152 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26546 p hg
    simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d15152, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26548 (p : Pattern) (guard : d16862 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15230 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26527 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15152 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26547 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26549 (p : Pattern) (guard : d16863 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16861 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26519 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16862 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26548 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26550 (p : Pattern) (guard : d1539 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26492 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26502 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26551 (p : Pattern) (guard : d1540 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25905 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25467 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26552 (p : Pattern) (guard : d1541 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26551 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26553 (p : Pattern) (guard : d1542 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26496 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26552 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26554 (p : Pattern) (guard : d1543 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26550 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26553 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26555 (p : Pattern) (guard : d1544 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26147 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26556 (p : Pattern) (guard : d1545 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26554 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26555 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26557 (p : Pattern) (guard : d1546 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26500 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26556 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26558 (p : Pattern) (guard : d1548 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26502 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26536 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26559 (p : Pattern) (guard : d1549 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26558 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26560 (p : Pattern) (guard : d1550 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26559 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26561 (p : Pattern) (guard : d1551 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26505 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26560 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26562 (p : Pattern) (guard : d1552 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26557 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26561 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26563 (p : Pattern) (guard : d1553 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26562 p hg
    simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1553, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26564 (p : Pattern) (guard : d1554 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26508 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26563 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26565 (p : Pattern) (guard : d1555 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26564 p hg
    simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1555, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26566 (p : Pattern) (guard : d1556 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26565 p hg
    simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1556, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26567 (p : Pattern) (guard : d1557 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26566 p hg
    simpa only [d1557, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26568 (p : Pattern) (guard : d1558 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26567 p hg
    simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1558, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26569 (p : Pattern) (guard : d10073 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26563 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26542 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26570 (p : Pattern) (guard : d10074 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26569 p hg
    simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10074, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26571 (p : Pattern) (guard : d10076 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26570 p hg
    simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10076, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26572 (p : Pattern) (guard : d16787 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26571 p hg
    simpa only [d16787, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26573 (p : Pattern) (guard : d16788 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26572 p hg
    simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d16788, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26574 (p : Pattern) (guard : d16789 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26568 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26573 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26575 (p : Pattern) (guard : d10080 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26556 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26539 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26576 (p : Pattern) (guard : d10081 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26560 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26577 (p : Pattern) (guard : d10082 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26575 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26576 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26578 (p : Pattern) (guard : d10083 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26577 p hg
    simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10083, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26579 (p : Pattern) (guard : d1563 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26536 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26580 (p : Pattern) (guard : d5128 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26579 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26581 (p : Pattern) (guard : d5129 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5128 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26580 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26582 (p : Pattern) (guard : d1564 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26579 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26583 (p : Pattern) (guard : d1565 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26582 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26584 (p : Pattern) (guard : d5130 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5129 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26581 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26583 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26585 (p : Pattern) (guard : d1578 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26583 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26586 (p : Pattern) (guard : d5131 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5130 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26584 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26585 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26587 (p : Pattern) (guard : d5132 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5131 p = 1 := by simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26586 p hg
    simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d5132, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26588 (p : Pattern) (guard : d10084 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26578 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26587 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26589 (p : Pattern) (guard : d10085 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26588 p hg
    simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10085, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26590 (p : Pattern) (guard : d10087 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26589 p hg
    simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10087, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26591 (p : Pattern) (guard : d15156 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26590 p hg
    simpa only [d15156, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26592 (p : Pattern) (guard : d15157 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26591 p hg
    simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d15157, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26593 (p : Pattern) (guard : d16790 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26547 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26592 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26594 (p : Pattern) (guard : d16791 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26574 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26593 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26595 (p : Pattern) (guard : d16864 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16863 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26549 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16791 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26594 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26596 (p : Pattern) (guard : d16865 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16865, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16865, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16864 p = 1 := by simpa only [d16865, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26595 p hg
    simpa only [d16865, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26597 (p : Pattern) (guard : d16866 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16866, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16866, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16865 p = 1 := by simpa only [d16866, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26596 p hg
    simpa only [d16866, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26598 (p : Pattern) (guard : d10095 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26500 p hg
    simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10056 p = 1 := by simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26535 p hg
    simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26599 (p : Pattern) (guard : d10096 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10095 p = 1 := by simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26598 p hg
    simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26600 (p : Pattern) (guard : d10097 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10096 p = 1 := by simpa only [d10097, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26599 p hg
    simpa only [d10097, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10097, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10097, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26601 (p : Pattern) (guard : d10098 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10097 p = 1 := by simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26600 p hg
    simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26542 p hg
    simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26602 (p : Pattern) (guard : d10099 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10098 p = 1 := by simpa only [d10099, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26601 p hg
    simpa only [d10099, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10099, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10099, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26603 (p : Pattern) (guard : d10101 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10099 p = 1 := by simpa only [d10101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26602 p hg
    simpa only [d10101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26604 (p : Pattern) (guard : d13348 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13348, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d13348, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10101 p = 1 := by simpa only [d13348, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26603 p hg
    simpa only [d13348, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26605 (p : Pattern) (guard : d13349 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13348 p = 1 := by simpa only [d13349, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26604 p hg
    simpa only [d13349, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13349, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d13349, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26606 (p : Pattern) (guard : d16867 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13349 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26605 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26592 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26607 (p : Pattern) (guard : d15158 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26592 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26608 (p : Pattern) (guard : d16868 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16867 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26606 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26607 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26609 (p : Pattern) (guard : d16869 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26594 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16868 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26608 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26610 (p : Pattern) (guard : d16870 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16869 p = 1 := by simpa only [d16870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d16870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26611 (p : Pattern) (guard : d16871 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16870 p = 1 := by simpa only [d16871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26610 p hg
    simpa only [d16871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26612 (p : Pattern) (guard : d16872 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16866 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26597 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16871 p = 1 := by simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26611 p hg
    simpa only [d16872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26613 (p : Pattern) (guard : d1559 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26552 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26614 (p : Pattern) (guard : d1560 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26558 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26613 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26615 (p : Pattern) (guard : d1561 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26614 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26168 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26616 (p : Pattern) (guard : d1562 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26556 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26615 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26617 (p : Pattern) (guard : d1566 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26560 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26583 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26618 (p : Pattern) (guard : d1567 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26616 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26617 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26619 (p : Pattern) (guard : d1568 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26618 p hg
    simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1568, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26620 (p : Pattern) (guard : d1569 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26563 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26619 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26621 (p : Pattern) (guard : d1570 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26620 p hg
    simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1570, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26622 (p : Pattern) (guard : d1571 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26621 p hg
    simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1571, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26623 (p : Pattern) (guard : d1572 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26622 p hg
    simpa only [d1572, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26624 (p : Pattern) (guard : d1573 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26623 p hg
    simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1573, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26625 (p : Pattern) (guard : d10114 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26619 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26587 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26626 (p : Pattern) (guard : d10115 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26625 p hg
    simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10115, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26627 (p : Pattern) (guard : d10117 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26626 p hg
    simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10117, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26628 (p : Pattern) (guard : d16792 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d16792, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26629 (p : Pattern) (guard : d16793 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26628 p hg
    simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d16793, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26630 (p : Pattern) (guard : d16794 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26624 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26629 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26631 (p : Pattern) (guard : d16795 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26630 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26607 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26632 (p : Pattern) (guard : d16796 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26594 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26631 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26633 (p : Pattern) (guard : d16797 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26632 p hg
    simpa only [d16797, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26634 (p : Pattern) (guard : d16798 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26633 p hg
    simpa only [d16798, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26635 (p : Pattern) (guard : d5123 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26537 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26579 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26636 (p : Pattern) (guard : d5124 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5123 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26635 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26637 (p : Pattern) (guard : d5125 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26556 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5124 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26638 (p : Pattern) (guard : d5126 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5125 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26637 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26617 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26639 (p : Pattern) (guard : d5127 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5126 p = 1 := by simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26638 p hg
    simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d5127, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26640 (p : Pattern) (guard : d5133 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5127 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26639 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26587 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26641 (p : Pattern) (guard : d5134 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26640 p hg
    simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d5134, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26642 (p : Pattern) (guard : d5135 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26641 p hg
    simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d5135, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26643 (p : Pattern) (guard : d5136 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26642 p hg
    simpa only [d5136, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26644 (p : Pattern) (guard : d5137 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d5137, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26645 (p : Pattern) (guard : d5138 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26646 (p : Pattern) (guard : d1575 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26613 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26647 (p : Pattern) (guard : d1576 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26646 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26168 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26648 (p : Pattern) (guard : d1593 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26647 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26649 (p : Pattern) (guard : d10129 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1559 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26613 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26650 (p : Pattern) (guard : d10130 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10129 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26651 (p : Pattern) (guard : d10131 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10130 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26650 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26652 (p : Pattern) (guard : d10132 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26648 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10131 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26651 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26653 (p : Pattern) (guard : d10133 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10132 p = 1 := by simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26652 p hg
    simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10133, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26654 (p : Pattern) (guard : d10134 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10133 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26653 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26655 (p : Pattern) (guard : d10135 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26654 p hg
    simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26656 (p : Pattern) (guard : d10137 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26657 (p : Pattern) (guard : d15163 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26656 p hg
    simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26658 (p : Pattern) (guard : d15164 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26657 p hg
    simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26659 (p : Pattern) (guard : d15165 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26658 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26660 (p : Pattern) (guard : d15166 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26645 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26659 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26661 (p : Pattern) (guard : d16799 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26631 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26660 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26662 (p : Pattern) (guard : d16800 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26661 p hg
    simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26663 (p : Pattern) (guard : d16801 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26662 p hg
    simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26664 (p : Pattern) (guard : d16802 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26634 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26663 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26665 (p : Pattern) (guard : d16873 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16872 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26612 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16802 p = 1 := by simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26664 p hg
    simpa only [d16873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26666 (p : Pattern) (guard : d1660 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1201 p = 1 := by simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26246 p hg
    simpa only [d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26667 (p : Pattern) (guard : d1661 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1205 p = 1 := by simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26250 p hg
    simpa only [d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26668 (p : Pattern) (guard : d1662 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1660 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26666 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1661 p = 1 := by simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26667 p hg
    simpa only [d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26669 (p : Pattern) (guard : d1663 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1662 p = 1 := by simpa only [d1663, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26668 p hg
    simpa only [d1663, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1663, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1663, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26670 (p : Pattern) (guard : d1520 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25658 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25977 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26671 (p : Pattern) (guard : d1521 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25775 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26670 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26672 (p : Pattern) (guard : d1522 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25957 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26671 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26673 (p : Pattern) (guard : d1523 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26254 p hg
    simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25657 p hg
    simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26674 (p : Pattern) (guard : d1524 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26673 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26255 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26675 (p : Pattern) (guard : d1525 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26674 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26676 (p : Pattern) (guard : d1526 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26675 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26677 (p : Pattern) (guard : d1527 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26672 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26676 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26678 (p : Pattern) (guard : d1528 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26258 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26679 (p : Pattern) (guard : d1529 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26677 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26678 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26680 (p : Pattern) (guard : d1530 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26246 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26679 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26681 (p : Pattern) (guard : d1532 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26670 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25978 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26682 (p : Pattern) (guard : d1533 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25963 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26683 (p : Pattern) (guard : d1534 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26682 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26684 (p : Pattern) (guard : d1535 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26683 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26685 (p : Pattern) (guard : d1536 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26250 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26684 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26686 (p : Pattern) (guard : d1537 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26680 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26685 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26687 (p : Pattern) (guard : d1538 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26686 p hg
    simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26688 (p : Pattern) (guard : d1664 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1663 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26669 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1538 p = 1 := by simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26687 p hg
    simpa only [d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26689 (p : Pattern) (guard : d1665 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1664 p = 1 := by simpa only [d1665, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26688 p hg
    simpa only [d1665, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1665, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1665, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26690 (p : Pattern) (guard : d1666 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1665 p = 1 := by simpa only [d1666, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26689 p hg
    simpa only [d1666, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1666, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1666, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26691 (p : Pattern) (guard : d1667 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1667, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1667, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1666 p = 1 := by simpa only [d1667, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26690 p hg
    simpa only [d1667, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26692 (p : Pattern) (guard : d1668 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1667 p = 1 := by simpa only [d1668, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26691 p hg
    simpa only [d1668, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1668, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1668, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26693 (p : Pattern) (guard : d10035 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26687 p hg
    simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d10035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26694 (p : Pattern) (guard : d10036 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10035 p = 1 := by simpa only [d10036, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26693 p hg
    simpa only [d10036, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10036, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10036, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26695 (p : Pattern) (guard : d10038 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10036 p = 1 := by simpa only [d10038, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26694 p hg
    simpa only [d10038, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10038, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10038, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26696 (p : Pattern) (guard : d16859 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16859, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d16859, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10038 p = 1 := by simpa only [d16859, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26695 p hg
    simpa only [d16859, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26697 (p : Pattern) (guard : d16860 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16859 p = 1 := by simpa only [d16860, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26696 p hg
    simpa only [d16860, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16860, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d16860, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26698 (p : Pattern) (guard : d16861 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1668 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26692 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16860 p = 1 := by simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26697 p hg
    simpa only [d16861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26699 (p : Pattern) (guard : d10042 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26246 p hg
    simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26700 (p : Pattern) (guard : d10043 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10042 p = 1 := by simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26699 p hg
    simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26701 (p : Pattern) (guard : d10044 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10043 p = 1 := by simpa only [d10044, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26700 p hg
    simpa only [d10044, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10044, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10044, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26702 (p : Pattern) (guard : d10045 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10044 p = 1 := by simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26701 p hg
    simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d10045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26703 (p : Pattern) (guard : d10046 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10045 p = 1 := by simpa only [d10046, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26702 p hg
    simpa only [d10046, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10046, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10046, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26704 (p : Pattern) (guard : d10048 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10046 p = 1 := by simpa only [d10048, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26703 p hg
    simpa only [d10048, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10048, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10048, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26705 (p : Pattern) (guard : d15229 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15229, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d15229, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10048 p = 1 := by simpa only [d15229, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26704 p hg
    simpa only [d15229, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26706 (p : Pattern) (guard : d15230 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15229 p = 1 := by simpa only [d15230, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26705 p hg
    simpa only [d15230, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15230, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d15230, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26707 (p : Pattern) (guard : d10051 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26679 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26708 (p : Pattern) (guard : d10052 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10051 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26707 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26709 (p : Pattern) (guard : d10053 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10052 p = 1 := by simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26708 p hg
    simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26710 (p : Pattern) (guard : d2005 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26673 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26711 (p : Pattern) (guard : d2006 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26710 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26712 (p : Pattern) (guard : d10054 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26711 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26713 (p : Pattern) (guard : d10055 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26712 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26714 (p : Pattern) (guard : d10056 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10055 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26713 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26715 (p : Pattern) (guard : d1547 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25978 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26716 (p : Pattern) (guard : d5122 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25975 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26715 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26717 (p : Pattern) (guard : d10057 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26718 (p : Pattern) (guard : d10058 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26717 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26719 (p : Pattern) (guard : d10059 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10056 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26714 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26718 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26720 (p : Pattern) (guard : d10060 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10059 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26719 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26721 (p : Pattern) (guard : d10061 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10060 p = 1 := by simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26720 p hg
    simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26722 (p : Pattern) (guard : d10062 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10053 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26709 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26721 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26723 (p : Pattern) (guard : d10063 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26722 p hg
    simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26724 (p : Pattern) (guard : d10065 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26723 p hg
    simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26725 (p : Pattern) (guard : d15151 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26724 p hg
    simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26726 (p : Pattern) (guard : d15152 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26725 p hg
    simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26727 (p : Pattern) (guard : d16862 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15230 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26706 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15152 p = 1 := by simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26726 p hg
    simpa only [d16862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26728 (p : Pattern) (guard : d16863 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16861 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26698 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16862 p = 1 := by simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26727 p hg
    simpa only [d16863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26729 (p : Pattern) (guard : d1539 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26671 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26730 (p : Pattern) (guard : d1540 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25977 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25499 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26731 (p : Pattern) (guard : d1541 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26730 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26732 (p : Pattern) (guard : d1542 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26675 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26731 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26733 (p : Pattern) (guard : d1543 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26729 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26732 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26734 (p : Pattern) (guard : d1544 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26302 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26735 (p : Pattern) (guard : d1545 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26733 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26734 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26736 (p : Pattern) (guard : d1546 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26679 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26735 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26737 (p : Pattern) (guard : d1548 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26715 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26738 (p : Pattern) (guard : d1549 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26737 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26739 (p : Pattern) (guard : d1550 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26738 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26740 (p : Pattern) (guard : d1551 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26684 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26739 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26741 (p : Pattern) (guard : d1552 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26736 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26740 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26742 (p : Pattern) (guard : d1553 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26741 p hg
    simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26743 (p : Pattern) (guard : d1554 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26687 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26742 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26744 (p : Pattern) (guard : d1555 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26743 p hg
    simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26745 (p : Pattern) (guard : d1556 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26744 p hg
    simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26746 (p : Pattern) (guard : d1557 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26745 p hg
    simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26747 (p : Pattern) (guard : d1558 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26746 p hg
    simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26748 (p : Pattern) (guard : d10073 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26742 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26721 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26749 (p : Pattern) (guard : d10074 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26748 p hg
    simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
