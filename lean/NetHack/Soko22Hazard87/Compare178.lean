import NetHack.Soko22Hazard87.Compare177
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44500 (p : Pattern) (guard : d367007 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367006 p = 1 := by simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44499 p hg
    simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44501 (p : Pattern) (guard : d367008 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367007 p = 1 := by simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44500 p hg
    simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366927 p = 1 := by simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44397 p hg
    simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44502 (p : Pattern) (guard : d367009 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367008 p = 1 := by simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44501 p hg
    simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44503 (p : Pattern) (guard : d367010 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44392 p hg
    simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44504 (p : Pattern) (guard : d367011 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367010 p = 1 := by simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44503 p hg
    simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44505 (p : Pattern) (guard : d367012 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367011 p = 1 := by simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44504 p hg
    simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44506 (p : Pattern) (guard : d367013 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367012 p = 1 := by simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44505 p hg
    simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44507 (p : Pattern) (guard : d367014 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367013 p = 1 := by simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44506 p hg
    simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44508 (p : Pattern) (guard : d367015 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367014 p = 1 := by simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44507 p hg
    simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44509 (p : Pattern) (guard : d367016 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367009 p = 1 := by simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44502 p hg
    simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367015 p = 1 := by simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44508 p hg
    simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44510 (p : Pattern) (guard : d367017 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366967 p = 1 := by simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44495 p hg
    simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367016 p = 1 := by simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44509 p hg
    simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44511 (p : Pattern) (guard : d367018 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366958 p = 1 := by simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44486 p hg
    simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367017 p = 1 := by simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44510 p hg
    simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44512 (p : Pattern) (guard : d367020 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366951 p = 1 := by simpa only [d367020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44418 p hg
    simpa only [d367020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44513 (p : Pattern) (guard : d367021 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366953 p = 1 := by simpa only [d367021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44420 p hg
    simpa only [d367021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44514 (p : Pattern) (guard : d367022 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367020 p = 1 := by simpa only [d367022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44512 p hg
    simpa only [d367022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367021 p = 1 := by simpa only [d367022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44513 p hg
    simpa only [d367022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44515 (p : Pattern) (guard : d367023 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367022 p = 1 := by simpa only [d367023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44514 p hg
    simpa only [d367023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44516 (p : Pattern) (guard : d367024 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367023 p = 1 := by simpa only [d367024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44515 p hg
    simpa only [d367024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44517 (p : Pattern) (guard : d367025 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367024 p = 1 := by simpa only [d367025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44516 p hg
    simpa only [d367025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44518 (p : Pattern) (guard : d367026 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366960 p = 1 := by simpa only [d367026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44427 p hg
    simpa only [d367026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44519 (p : Pattern) (guard : d367027 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366963 p = 1 := by simpa only [d367027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d367027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44520 (p : Pattern) (guard : d367028 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367026 p = 1 := by simpa only [d367028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44518 p hg
    simpa only [d367028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367027 p = 1 := by simpa only [d367028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44519 p hg
    simpa only [d367028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44521 (p : Pattern) (guard : d367029 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367028 p = 1 := by simpa only [d367029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44520 p hg
    simpa only [d367029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44522 (p : Pattern) (guard : d367030 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367029 p = 1 := by simpa only [d367030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44521 p hg
    simpa only [d367030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44523 (p : Pattern) (guard : d367031 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367006 p = 1 := by simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44465 p hg
    simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44524 (p : Pattern) (guard : d367032 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367031 p = 1 := by simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44523 p hg
    simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366940 p = 1 := by simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44407 p hg
    simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44525 (p : Pattern) (guard : d367033 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367032 p = 1 := by simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44524 p hg
    simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44526 (p : Pattern) (guard : d367034 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367012 p = 1 := by simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44471 p hg
    simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44527 (p : Pattern) (guard : d367035 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367034 p = 1 := by simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44528 (p : Pattern) (guard : d367036 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367035 p = 1 := by simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44527 p hg
    simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44529 (p : Pattern) (guard : d367037 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367033 p = 1 := by simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367036 p = 1 := by simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44528 p hg
    simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44530 (p : Pattern) (guard : d367038 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d367030 p = 1 := by simpa only [d367038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44522 p hg
    simpa only [d367038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367037 p = 1 := by simpa only [d367038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44529 p hg
    simpa only [d367038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44531 (p : Pattern) (guard : d367039 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d367025 p = 1 := by simpa only [d367039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44517 p hg
    simpa only [d367039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367038 p = 1 := by simpa only [d367039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44530 p hg
    simpa only [d367039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44532 (p : Pattern) (guard : d367040 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d367018 p = 1 := by simpa only [d367040, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44511 p hg
    simpa only [d367040, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367039 p = 1 := by simpa only [d367040, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44531 p hg
    simpa only [d367040, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44533 (p : Pattern) (guard : d367041 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d367019 p = 1 := by simpa only [d367041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d367041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367040 p = 1 := by simpa only [d367041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44532 p hg
    simpa only [d367041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44534 (p : Pattern) (guard : d367042 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366931 p = 1 := by simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44383 p hg
    simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44535 (p : Pattern) (guard : d367043 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367042 p = 1 := by simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44534 p hg
    simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44536 (p : Pattern) (guard : d367044 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367043 p = 1 := by simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44535 p hg
    simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44537 (p : Pattern) (guard : d367045 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367044 p = 1 := by simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44536 p hg
    simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44538 (p : Pattern) (guard : d367046 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367045 p = 1 := by simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44537 p hg
    simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44539 (p : Pattern) (guard : d367047 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366936 p = 1 := by simpa only [d367047, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44406 p hg
    simpa only [d367047, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367046 p = 1 := by simpa only [d367047, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44538 p hg
    simpa only [d367047, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44540 (p : Pattern) (guard : d367042 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366931 p = 1 := by simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44401 p hg
    simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44541 (p : Pattern) (guard : d367043 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367042 p = 1 := by simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44540 p hg
    simpa only [d367043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44542 (p : Pattern) (guard : d367044 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367043 p = 1 := by simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44541 p hg
    simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44543 (p : Pattern) (guard : d367045 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367044 p = 1 := by simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44542 p hg
    simpa only [d367045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44544 (p : Pattern) (guard : d367046 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367045 p = 1 := by simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44543 p hg
    simpa only [d367046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44545 (p : Pattern) (guard : d367048 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366941 p = 1 := by simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44408 p hg
    simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44546 (p : Pattern) (guard : d367049 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367048 p = 1 := by simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44545 p hg
    simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44547 (p : Pattern) (guard : d367050 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367049 p = 1 := by simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44546 p hg
    simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44548 (p : Pattern) (guard : d367051 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367050 p = 1 := by simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44547 p hg
    simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44549 (p : Pattern) (guard : d367052 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367051 p = 1 := by simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44548 p hg
    simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44550 (p : Pattern) (guard : d367053 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d367046 p = 1 := by simpa only [d367053, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44544 p hg
    simpa only [d367053, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367052 p = 1 := by simpa only [d367053, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44549 p hg
    simpa only [d367053, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44551 (p : Pattern) (guard : d367054 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d367047 p = 1 := by simpa only [d367054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44539 p hg
    simpa only [d367054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367053 p = 1 := by simpa only [d367054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44550 p hg
    simpa only [d367054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44552 (p : Pattern) (guard : d367055 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367041 p = 1 := by simpa only [d367055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44533 p hg
    simpa only [d367055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367054 p = 1 := by simpa only [d367055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d367055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44553 (p : Pattern) (guard : d367056 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367055 p = 1 := by simpa only [d367056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44552 p hg
    simpa only [d367056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d367056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44554 (p : Pattern) (guard : d367057 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366950 p = 1 := by simpa only [d367057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44417 p hg
    simpa only [d367057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367056 p = 1 := by simpa only [d367057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44553 p hg
    simpa only [d367057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44555 (p : Pattern) (guard : d312059 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44556 (p : Pattern) (guard : d312060 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d312060, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d312060, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d312059 p = 1 := by simpa only [d312060, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44555 p hg
    simpa only [d312060, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44557 (p : Pattern) (guard : d312061 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d312060 p = 1 := by simpa only [d312061, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44556 p hg
    simpa only [d312061, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d312061, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d312061, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44558 (p : Pattern) (guard : d366970 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44559 (p : Pattern) (guard : d366971 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366971, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366971, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366970 p = 1 := by simpa only [d366971, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44558 p hg
    simpa only [d366971, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44560 (p : Pattern) (guard : d366972 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366971 p = 1 := by simpa only [d366972, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44559 p hg
    simpa only [d366972, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366972, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366972, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44561 (p : Pattern) (guard : d366973 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d312061 p = 1 := by simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44557 p hg
    simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366972 p = 1 := by simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44560 p hg
    simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44562 (p : Pattern) (guard : d366976 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44563 (p : Pattern) (guard : d366977 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366977, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366977, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366976 p = 1 := by simpa only [d366977, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44562 p hg
    simpa only [d366977, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44564 (p : Pattern) (guard : d366978 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366977 p = 1 := by simpa only [d366978, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44563 p hg
    simpa only [d366978, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366978, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366978, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44565 (p : Pattern) (guard : d366884 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44566 (p : Pattern) (guard : d366885 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366884 p = 1 := by simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44565 p hg
    simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44567 (p : Pattern) (guard : d366886 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366885 p = 1 := by simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44566 p hg
    simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44568 (p : Pattern) (guard : d366979 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366978 p = 1 := by simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44564 p hg
    simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366886 p = 1 := by simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44567 p hg
    simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44569 (p : Pattern) (guard : d366980 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366973 p = 1 := by simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44561 p hg
    simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366979 p = 1 := by simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44568 p hg
    simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44570 (p : Pattern) (guard : d366862 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44571 (p : Pattern) (guard : d366863 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366862 p = 1 := by simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44570 p hg
    simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44572 (p : Pattern) (guard : d366864 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366863 p = 1 := by simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44571 p hg
    simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44573 (p : Pattern) (guard : d366875 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44574 (p : Pattern) (guard : d366876 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366875 p = 1 := by simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44573 p hg
    simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44575 (p : Pattern) (guard : d366877 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366876 p = 1 := by simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44574 p hg
    simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44576 (p : Pattern) (guard : d366878 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366864 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44572 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366877 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44575 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44577 (p : Pattern) (guard : d366894 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44578 (p : Pattern) (guard : d366895 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366894 p = 1 := by simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44577 p hg
    simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44579 (p : Pattern) (guard : d366896 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366895 p = 1 := by simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44578 p hg
    simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44580 (p : Pattern) (guard : d366897 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366886 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44567 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44581 (p : Pattern) (guard : d366898 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366878 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44576 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366897 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44580 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44582 (p : Pattern) (guard : d366981 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366980 p = 1 := by simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44569 p hg
    simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366898 p = 1 := by simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44581 p hg
    simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44583 (p : Pattern) (guard : d366982 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366982, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366982, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366981 p = 1 := by simpa only [d366982, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44582 p hg
    simpa only [d366982, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44584 (p : Pattern) (guard : d366983 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366983, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366983, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366982 p = 1 := by simpa only [d366983, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44583 p hg
    simpa only [d366983, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44585 (p : Pattern) (guard : d366991 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44586 (p : Pattern) (guard : d366992 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366992, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366992, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366991 p = 1 := by simpa only [d366992, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44585 p hg
    simpa only [d366992, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44587 (p : Pattern) (guard : d366993 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366992 p = 1 := by simpa only [d366993, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44586 p hg
    simpa only [d366993, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366993, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366993, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44588 (p : Pattern) (guard : d366994 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366993 p = 1 := by simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44587 p hg
    simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44589 (p : Pattern) (guard : d366905 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366896 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44590 (p : Pattern) (guard : d366995 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366994 p = 1 := by simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44588 p hg
    simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366905 p = 1 := by simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44589 p hg
    simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44591 (p : Pattern) (guard : d366996 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366898 p = 1 := by simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44581 p hg
    simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366995 p = 1 := by simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44590 p hg
    simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44592 (p : Pattern) (guard : d366997 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366997, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366997, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366996 p = 1 := by simpa only [d366997, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44591 p hg
    simpa only [d366997, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44593 (p : Pattern) (guard : d366998 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366998, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366998, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366997 p = 1 := by simpa only [d366998, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44592 p hg
    simpa only [d366998, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44594 (p : Pattern) (guard : d366999 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366983 p = 1 := by simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366998 p = 1 := by simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44593 p hg
    simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44595 (p : Pattern) (guard : d366901 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare44596 (p : Pattern) (guard : d366902 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366901 p = 1 := by simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44595 p hg
    simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44597 (p : Pattern) (guard : d366903 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366902 p = 1 := by simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44596 p hg
    simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44598 (p : Pattern) (guard : d366904 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366903 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44597 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44599 (p : Pattern) (guard : d366906 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366904 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44598 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366905 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44589 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44600 (p : Pattern) (guard : d366907 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366898 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44581 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366906 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44599 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44601 (p : Pattern) (guard : d366908 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366907 p = 1 := by simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44600 p hg
    simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44602 (p : Pattern) (guard : d366909 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366908 p = 1 := by simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44603 (p : Pattern) (guard : d366910 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366905 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44589 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44604 (p : Pattern) (guard : d366911 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366906 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44599 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366910 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44603 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44605 (p : Pattern) (guard : d366912 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366911 p = 1 := by simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44604 p hg
    simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44606 (p : Pattern) (guard : d366913 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366912 p = 1 := by simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44605 p hg
    simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44607 (p : Pattern) (guard : d366914 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366909 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44602 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366913 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44606 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44608 (p : Pattern) (guard : d367000 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366999 p = 1 := by simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44594 p hg
    simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366914 p = 1 := by simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44607 p hg
    simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44609 (p : Pattern) (guard : d367001 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367000 p = 1 := by simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44608 p hg
    simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44610 (p : Pattern) (guard : d367002 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367001 p = 1 := by simpa only [d367002, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44609 p hg
    simpa only [d367002, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367002, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d367002, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44611 (p : Pattern) (guard : d367003 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367003, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d367003, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367002 p = 1 := by simpa only [d367003, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44610 p hg
    simpa only [d367003, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44612 (p : Pattern) (guard : d366915 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366913 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44606 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44613 (p : Pattern) (guard : d366916 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366914 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44607 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366915 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44612 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44614 (p : Pattern) (guard : d366917 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366916 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44613 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44615 (p : Pattern) (guard : d366918 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366917 p = 1 := by simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44614 p hg
    simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44616 (p : Pattern) (guard : d366919 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366918 p = 1 := by simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44615 p hg
    simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44617 (p : Pattern) (guard : d367004 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367003 p = 1 := by simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44611 p hg
    simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366919 p = 1 := by simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44616 p hg
    simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44618 (p : Pattern) (guard : d367005 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367004 p = 1 := by simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44617 p hg
    simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44619 (p : Pattern) (guard : d367006 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367005 p = 1 := by simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44618 p hg
    simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44620 (p : Pattern) (guard : d367031 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367006 p = 1 := by simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44619 p hg
    simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44621 (p : Pattern) (guard : d366920 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366915 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44612 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44622 (p : Pattern) (guard : d366921 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366920 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44621 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44623 (p : Pattern) (guard : d366922 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366921 p = 1 := by simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44622 p hg
    simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44624 (p : Pattern) (guard : d366923 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366922 p = 1 := by simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44623 p hg
    simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44625 (p : Pattern) (guard : d366924 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44616 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366923 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44624 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44626 (p : Pattern) (guard : d366925 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366924 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44625 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44627 (p : Pattern) (guard : d366926 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366925 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44626 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44628 (p : Pattern) (guard : d366940 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366926 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44627 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44629 (p : Pattern) (guard : d367032 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367031 p = 1 := by simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44620 p hg
    simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366940 p = 1 := by simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44628 p hg
    simpa only [d367032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44630 (p : Pattern) (guard : d367033 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367032 p = 1 := by simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44629 p hg
    simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44631 (p : Pattern) (guard : d367010 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44616 p hg
    simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44632 (p : Pattern) (guard : d367011 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367010 p = 1 := by simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44631 p hg
    simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44633 (p : Pattern) (guard : d367012 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367011 p = 1 := by simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44632 p hg
    simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44634 (p : Pattern) (guard : d367034 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367012 p = 1 := by simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44633 p hg
    simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44635 (p : Pattern) (guard : d367035 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367034 p = 1 := by simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44634 p hg
    simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44636 (p : Pattern) (guard : d367036 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367035 p = 1 := by simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44635 p hg
    simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44637 (p : Pattern) (guard : d367037 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367033 p = 1 := by simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44630 p hg
    simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367036 p = 1 := by simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44636 p hg
    simpa only [d367037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44638 (p : Pattern) (guard : d367058 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367037 p = 1 := by simpa only [d367058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44637 p hg
    simpa only [d367058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44639 (p : Pattern) (guard : d367059 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367058 p = 1 := by simpa only [d367059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44638 p hg
    simpa only [d367059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44640 (p : Pattern) (guard : d367060 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367060, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367060, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367059 p = 1 := by simpa only [d367060, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44639 p hg
    simpa only [d367060, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44641 (p : Pattern) (guard : d367061 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367060 p = 1 := by simpa only [d367061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44640 p hg
    simpa only [d367061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44642 (p : Pattern) (guard : d366928 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366923 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44624 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44643 (p : Pattern) (guard : d366929 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366928 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44642 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44644 (p : Pattern) (guard : d366930 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366929 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44643 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44645 (p : Pattern) (guard : d366941 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366930 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44644 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44646 (p : Pattern) (guard : d367048 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366941 p = 1 := by simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44645 p hg
    simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44647 (p : Pattern) (guard : d367049 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367048 p = 1 := by simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44646 p hg
    simpa only [d367049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44648 (p : Pattern) (guard : d367050 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367049 p = 1 := by simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44647 p hg
    simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44649 (p : Pattern) (guard : d367051 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367050 p = 1 := by simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44648 p hg
    simpa only [d367051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44650 (p : Pattern) (guard : d367052 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367051 p = 1 := by simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44649 p hg
    simpa only [d367052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44651 (p : Pattern) (guard : d367062 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367062, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367062, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367052 p = 1 := by simpa only [d367062, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44650 p hg
    simpa only [d367062, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44652 (p : Pattern) (guard : d367063 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367062 p = 1 := by simpa only [d367063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44651 p hg
    simpa only [d367063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44653 (p : Pattern) (guard : d367064 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367061 p = 1 := by simpa only [d367064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44641 p hg
    simpa only [d367064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367063 p = 1 := by simpa only [d367064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44652 p hg
    simpa only [d367064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44654 (p : Pattern) (guard : d367065 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367064 p = 1 := by simpa only [d367065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44653 p hg
    simpa only [d367065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44655 (p : Pattern) (guard : d367066 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367065 p = 1 := by simpa only [d367066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44654 p hg
    simpa only [d367066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44656 (p : Pattern) (guard : d367067 p = 1) : d51470 p ≤ (8 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367057 p = 1 := by simpa only [d367067, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44554 p hg
    simpa only [d367067, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367066 p = 1 := by simpa only [d367067, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44655 p hg
    simpa only [d367067, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44657 (p : Pattern) (guard : d2006 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43393 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44658 (p : Pattern) (guard : d2007 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44657 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44659 (p : Pattern) (guard : d2008 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44658 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44660 (p : Pattern) (guard : d34782 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2008 p = 1 := by simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44659 p hg
    simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44661 (p : Pattern) (guard : d34783 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34782 p = 1 := by simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44660 p hg
    simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44662 (p : Pattern) (guard : d43846 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2007 p = 1 := by simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44658 p hg
    simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44663 (p : Pattern) (guard : d43847 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d43846 p = 1 := by simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44664 (p : Pattern) (guard : d43848 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43847 p = 1 := by simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44665 (p : Pattern) (guard : d311925 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d34783 p = 1 := by simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44661 p hg
    simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43848 p = 1 := by simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44664 p hg
    simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44666 (p : Pattern) (guard : d311926 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d311925 p = 1 := by simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44665 p hg
    simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44667 (p : Pattern) (guard : d312057 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d312057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d312057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311926 p = 1 := by simpa only [d312057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44666 p hg
    simpa only [d312057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44668 (p : Pattern) (guard : d312184 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d312184, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d312184, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d312057 p = 1 := by simpa only [d312184, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44667 p hg
    simpa only [d312184, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44669 (p : Pattern) (guard : d312058 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44670 (p : Pattern) (guard : d312185 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d312184 p = 1 := by simpa only [d312185, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d312185, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d312058 p = 1 := by simpa only [d312185, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44669 p hg
    simpa only [d312185, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44671 (p : Pattern) (guard : d312059 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44672 (p : Pattern) (guard : d312186 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d312185 p = 1 := by simpa only [d312186, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d312186, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d312059 p = 1 := by simpa only [d312186, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44671 p hg
    simpa only [d312186, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44673 (p : Pattern) (guard : d312187 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d312186 p = 1 := by simpa only [d312187, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44672 p hg
    simpa only [d312187, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d312187, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d312187, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44674 (p : Pattern) (guard : d366968 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d311926 p = 1 := by simpa only [d366968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44666 p hg
    simpa only [d366968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366640 p = 1 := by simpa only [d366968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44183 p hg
    simpa only [d366968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44675 (p : Pattern) (guard : d367068 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367068, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367068, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366968 p = 1 := by simpa only [d367068, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44674 p hg
    simpa only [d367068, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44676 (p : Pattern) (guard : d366969 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44677 (p : Pattern) (guard : d367069 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367068 p = 1 := by simpa only [d367069, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44675 p hg
    simpa only [d367069, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366969 p = 1 := by simpa only [d367069, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44676 p hg
    simpa only [d367069, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44678 (p : Pattern) (guard : d366970 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44679 (p : Pattern) (guard : d367070 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367069 p = 1 := by simpa only [d367070, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44677 p hg
    simpa only [d367070, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366970 p = 1 := by simpa only [d367070, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44678 p hg
    simpa only [d367070, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44680 (p : Pattern) (guard : d367071 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367070 p = 1 := by simpa only [d367071, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44679 p hg
    simpa only [d367071, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367071, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367071, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44681 (p : Pattern) (guard : d367072 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d312187 p = 1 := by simpa only [d367072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44673 p hg
    simpa only [d367072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367071 p = 1 := by simpa only [d367072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44680 p hg
    simpa only [d367072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44682 (p : Pattern) (guard : d366974 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d366974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366640 p = 1 := by simpa only [d366974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44183 p hg
    simpa only [d366974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44683 (p : Pattern) (guard : d367073 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367073, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367073, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366974 p = 1 := by simpa only [d367073, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44682 p hg
    simpa only [d367073, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44684 (p : Pattern) (guard : d366975 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44685 (p : Pattern) (guard : d367074 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367073 p = 1 := by simpa only [d367074, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44683 p hg
    simpa only [d367074, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366975 p = 1 := by simpa only [d367074, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44684 p hg
    simpa only [d367074, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44686 (p : Pattern) (guard : d366976 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44687 (p : Pattern) (guard : d367075 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367074 p = 1 := by simpa only [d367075, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44685 p hg
    simpa only [d367075, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366976 p = 1 := by simpa only [d367075, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44686 p hg
    simpa only [d367075, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44688 (p : Pattern) (guard : d367076 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367075 p = 1 := by simpa only [d367076, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44687 p hg
    simpa only [d367076, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367076, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367076, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44689 (p : Pattern) (guard : d366879 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34782 p = 1 := by simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44660 p hg
    simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308524 p = 1 := by simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44169 p hg
    simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44690 (p : Pattern) (guard : d366880 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366879 p = 1 := by simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44689 p hg
    simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44691 (p : Pattern) (guard : d366881 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366880 p = 1 := by simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44690 p hg
    simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44692 (p : Pattern) (guard : d366868 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32698 p = 1 := by simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44167 p hg
    simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32153 p = 1 := by simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43734 p hg
    simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44693 (p : Pattern) (guard : d0 p = 1) : d51182 p ≤ (8 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44694 (p : Pattern) (guard : d1086 p = 1) : d51183 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42999 p hg
    simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44693 p hg
    simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44695 (p : Pattern) (guard : d0 p = 1) : d51185 p ≤ (8 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44696 (p : Pattern) (guard : d9771 p = 1) : d51186 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44694 p hg
    simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44695 p hg
    simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44697 (p : Pattern) (guard : d32155 p = 1) : d51186 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44696 p hg
    simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44698 (p : Pattern) (guard : d366869 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366868 p = 1 := by simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44692 p hg
    simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44697 p hg
    simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44699 (p : Pattern) (guard : d10054 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44657 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44700 (p : Pattern) (guard : d343143 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d10054 p = 1 := by simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44699 p hg
    simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44701 (p : Pattern) (guard : d343144 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d343143 p = 1 := by simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44700 p hg
    simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44702 (p : Pattern) (guard : d366870 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366869 p = 1 := by simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44698 p hg
    simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44701 p hg
    simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44703 (p : Pattern) (guard : d366871 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366870 p = 1 := by simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44704 (p : Pattern) (guard : d366872 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366871 p = 1 := by simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44703 p hg
    simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44705 (p : Pattern) (guard : d366882 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366881 p = 1 := by simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44691 p hg
    simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366872 p = 1 := by simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44704 p hg
    simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44706 (p : Pattern) (guard : d367077 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366882 p = 1 := by simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44705 p hg
    simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44707 (p : Pattern) (guard : d366883 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44708 (p : Pattern) (guard : d367078 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367077 p = 1 := by simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44706 p hg
    simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366883 p = 1 := by simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44707 p hg
    simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44709 (p : Pattern) (guard : d366884 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44710 (p : Pattern) (guard : d367079 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367078 p = 1 := by simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44708 p hg
    simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366884 p = 1 := by simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44709 p hg
    simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44711 (p : Pattern) (guard : d367080 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367079 p = 1 := by simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44710 p hg
    simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44712 (p : Pattern) (guard : d367081 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367076 p = 1 := by simpa only [d367081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44688 p hg
    simpa only [d367081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367080 p = 1 := by simpa only [d367081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44711 p hg
    simpa only [d367081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44713 (p : Pattern) (guard : d367082 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367072 p = 1 := by simpa only [d367082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44681 p hg
    simpa only [d367082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367081 p = 1 := by simpa only [d367082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44712 p hg
    simpa only [d367082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44714 (p : Pattern) (guard : d43867 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43392 p hg
    simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44657 p hg
    simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44715 (p : Pattern) (guard : d366854 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44714 p hg
    simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44699 p hg
    simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44716 (p : Pattern) (guard : d366855 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366854 p = 1 := by simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44715 p hg
    simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44717 (p : Pattern) (guard : d366856 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34782 p = 1 := by simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44660 p hg
    simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366855 p = 1 := by simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44716 p hg
    simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44718 (p : Pattern) (guard : d366857 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d43847 p = 1 := by simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44701 p hg
    simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44719 (p : Pattern) (guard : d366858 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366856 p = 1 := by simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44717 p hg
    simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366857 p = 1 := by simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44718 p hg
    simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44720 (p : Pattern) (guard : d366859 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366858 p = 1 := by simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44719 p hg
    simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44721 (p : Pattern) (guard : d366860 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d311926 p = 1 := by simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44666 p hg
    simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366859 p = 1 := by simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44722 (p : Pattern) (guard : d367083 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366860 p = 1 := by simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44721 p hg
    simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44723 (p : Pattern) (guard : d366861 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44724 (p : Pattern) (guard : d367084 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367083 p = 1 := by simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44722 p hg
    simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366861 p = 1 := by simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44723 p hg
    simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44725 (p : Pattern) (guard : d366862 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44726 (p : Pattern) (guard : d367085 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367084 p = 1 := by simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366862 p = 1 := by simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44725 p hg
    simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44727 (p : Pattern) (guard : d367086 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367085 p = 1 := by simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44726 p hg
    simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44728 (p : Pattern) (guard : d43868 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44714 p hg
    simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44729 (p : Pattern) (guard : d43869 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d43868 p = 1 := by simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44728 p hg
    simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44730 (p : Pattern) (guard : d366865 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d43869 p = 1 := by simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44729 p hg
    simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44701 p hg
    simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44731 (p : Pattern) (guard : d366866 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366856 p = 1 := by simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44717 p hg
    simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366865 p = 1 := by simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44730 p hg
    simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44732 (p : Pattern) (guard : d366867 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366866 p = 1 := by simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44731 p hg
    simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44733 (p : Pattern) (guard : d366873 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366867 p = 1 := by simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44732 p hg
    simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366872 p = 1 := by simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44704 p hg
    simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44734 (p : Pattern) (guard : d367087 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366873 p = 1 := by simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44733 p hg
    simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44735 (p : Pattern) (guard : d366874 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44736 (p : Pattern) (guard : d367088 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367087 p = 1 := by simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44734 p hg
    simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366874 p = 1 := by simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44735 p hg
    simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44737 (p : Pattern) (guard : d366875 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44738 (p : Pattern) (guard : d367089 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367088 p = 1 := by simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44736 p hg
    simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366875 p = 1 := by simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44737 p hg
    simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44739 (p : Pattern) (guard : d367090 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367089 p = 1 := by simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44738 p hg
    simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44740 (p : Pattern) (guard : d367091 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367086 p = 1 := by simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44727 p hg
    simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367090 p = 1 := by simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44739 p hg
    simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44741 (p : Pattern) (guard : d366887 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44714 p hg
    simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32153 p = 1 := by simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43734 p hg
    simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44742 (p : Pattern) (guard : d366888 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366887 p = 1 := by simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44741 p hg
    simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44697 p hg
    simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44743 (p : Pattern) (guard : d366889 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366888 p = 1 := by simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44742 p hg
    simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44701 p hg
    simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44744 (p : Pattern) (guard : d343638 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d343144 p = 1 := by simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44701 p hg
    simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44745 (p : Pattern) (guard : d366890 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366889 p = 1 := by simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44743 p hg
    simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343638 p = 1 := by simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44744 p hg
    simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44746 (p : Pattern) (guard : d366891 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366890 p = 1 := by simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44747 (p : Pattern) (guard : d366892 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366891 p = 1 := by simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44746 p hg
    simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44748 (p : Pattern) (guard : d367092 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366892 p = 1 := by simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44747 p hg
    simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44749 (p : Pattern) (guard : d366893 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
end NetHack.Soko22Hazard87
