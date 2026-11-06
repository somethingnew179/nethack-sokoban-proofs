import NetHack.Soko22Hazard87.Compare117
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29500 (p : Pattern) (guard : d259049 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259048 p = 1 := by simpa only [d259049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29499 p hg
    simpa only [d259049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29501 (p : Pattern) (guard : d259050 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258761 p = 1 := by simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29073 p hg
    simpa only [d259050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29502 (p : Pattern) (guard : d259051 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259050 p = 1 := by simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29501 p hg
    simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29503 (p : Pattern) (guard : d259052 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259051 p = 1 := by simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29502 p hg
    simpa only [d259052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29504 (p : Pattern) (guard : d259053 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259052 p = 1 := by simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29503 p hg
    simpa only [d259053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29505 (p : Pattern) (guard : d259054 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259053 p = 1 := by simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29504 p hg
    simpa only [d259054, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29506 (p : Pattern) (guard : d259055 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259054 p = 1 := by simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29505 p hg
    simpa only [d259055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29507 (p : Pattern) (guard : d259056 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259049 p = 1 := by simpa only [d259056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29500 p hg
    simpa only [d259056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259055 p = 1 := by simpa only [d259056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29506 p hg
    simpa only [d259056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29508 (p : Pattern) (guard : d259057 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259056 p = 1 := by simpa only [d259057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29507 p hg
    simpa only [d259057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29509 (p : Pattern) (guard : d259058 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259057 p = 1 := by simpa only [d259058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29508 p hg
    simpa only [d259058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29510 (p : Pattern) (guard : d259059 p = 1) : d47865 p ≤ (-1 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259058 p = 1 := by simpa only [d259059, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29509 p hg
    simpa only [d259059, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259059, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29083 p hg
    simpa only [d259059, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29511 (p : Pattern) (guard : d259060 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d259013 p = 1 := by simpa only [d259060, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29434 p hg
    simpa only [d259060, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259059 p = 1 := by simpa only [d259060, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29510 p hg
    simpa only [d259060, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29512 (p : Pattern) (guard : d259061 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259060 p = 1 := by simpa only [d259061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29511 p hg
    simpa only [d259061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29513 (p : Pattern) (guard : d259062 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259061 p = 1 := by simpa only [d259062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29512 p hg
    simpa only [d259062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29514 (p : Pattern) (guard : d259063 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259062 p = 1 := by simpa only [d259063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29513 p hg
    simpa only [d259063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29515 (p : Pattern) (guard : d259064 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259063 p = 1 := by simpa only [d259064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d259064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29516 (p : Pattern) (guard : d259065 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259064 p = 1 := by simpa only [d259065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29515 p hg
    simpa only [d259065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29517 (p : Pattern) (guard : d259066 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259065 p = 1 := by simpa only [d259066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29516 p hg
    simpa only [d259066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29518 (p : Pattern) (guard : d259067 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259066 p = 1 := by simpa only [d259067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29517 p hg
    simpa only [d259067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29519 (p : Pattern) (guard : d259068 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d258905 p = 1 := by simpa only [d259068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d259068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259067 p = 1 := by simpa only [d259068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d259068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29520 (p : Pattern) (guard : d259069 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29138 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29521 (p : Pattern) (guard : d259070 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258958 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29331 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259069 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29520 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29522 (p : Pattern) (guard : d259071 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259070 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29521 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29523 (p : Pattern) (guard : d259072 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259071 p = 1 := by simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29522 p hg
    simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29524 (p : Pattern) (guard : d259073 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259072 p = 1 := by simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29523 p hg
    simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29525 (p : Pattern) (guard : d259074 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259069 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29520 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29526 (p : Pattern) (guard : d259075 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259074 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29525 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29527 (p : Pattern) (guard : d259076 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259075 p = 1 := by simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29526 p hg
    simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29528 (p : Pattern) (guard : d259077 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259076 p = 1 := by simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29527 p hg
    simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29529 (p : Pattern) (guard : d259078 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259073 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29524 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259077 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29528 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29530 (p : Pattern) (guard : d259079 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259078 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29529 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29531 (p : Pattern) (guard : d259080 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259079 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29530 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29532 (p : Pattern) (guard : d259081 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259080 p = 1 := by simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29531 p hg
    simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29533 (p : Pattern) (guard : d259082 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259077 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29528 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29534 (p : Pattern) (guard : d259083 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259082 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29533 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29535 (p : Pattern) (guard : d259084 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259083 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29534 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29536 (p : Pattern) (guard : d259085 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259084 p = 1 := by simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29535 p hg
    simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29537 (p : Pattern) (guard : d259086 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259081 p = 1 := by simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29532 p hg
    simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259085 p = 1 := by simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29536 p hg
    simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29538 (p : Pattern) (guard : d259087 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259086 p = 1 := by simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29537 p hg
    simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29539 (p : Pattern) (guard : d259088 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259087 p = 1 := by simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29538 p hg
    simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29540 (p : Pattern) (guard : d259089 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259088 p = 1 := by simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29539 p hg
    simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29541 (p : Pattern) (guard : d259090 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259089 p = 1 := by simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29540 p hg
    simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29542 (p : Pattern) (guard : d259091 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259090 p = 1 := by simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29541 p hg
    simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29543 (p : Pattern) (guard : d259092 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259091 p = 1 := by simpa only [d259092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29542 p hg
    simpa only [d259092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29544 (p : Pattern) (guard : d259093 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259092 p = 1 := by simpa only [d259093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29543 p hg
    simpa only [d259093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29545 (p : Pattern) (guard : d259094 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259080 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29531 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29546 (p : Pattern) (guard : d259095 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259084 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29535 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29547 (p : Pattern) (guard : d259096 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259094 p = 1 := by simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29545 p hg
    simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259095 p = 1 := by simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29546 p hg
    simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29548 (p : Pattern) (guard : d259097 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259096 p = 1 := by simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29547 p hg
    simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29549 (p : Pattern) (guard : d259098 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259097 p = 1 := by simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29548 p hg
    simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29550 (p : Pattern) (guard : d259099 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259098 p = 1 := by simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29549 p hg
    simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29551 (p : Pattern) (guard : d259100 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259099 p = 1 := by simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29550 p hg
    simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29552 (p : Pattern) (guard : d259101 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259090 p = 1 := by simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29541 p hg
    simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259100 p = 1 := by simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29551 p hg
    simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29553 (p : Pattern) (guard : d259102 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259091 p = 1 := by simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29542 p hg
    simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259101 p = 1 := by simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29552 p hg
    simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29554 (p : Pattern) (guard : d259103 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259102 p = 1 := by simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29553 p hg
    simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29555 (p : Pattern) (guard : d259104 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259093 p = 1 := by simpa only [d259104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29544 p hg
    simpa only [d259104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259103 p = 1 := by simpa only [d259104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29554 p hg
    simpa only [d259104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29556 (p : Pattern) (guard : d259105 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259079 p = 1 := by simpa only [d259105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29530 p hg
    simpa only [d259105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29557 (p : Pattern) (guard : d259106 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259105 p = 1 := by simpa only [d259106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29556 p hg
    simpa only [d259106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29558 (p : Pattern) (guard : d259107 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259083 p = 1 := by simpa only [d259107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29534 p hg
    simpa only [d259107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29559 (p : Pattern) (guard : d259108 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259107 p = 1 := by simpa only [d259108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29558 p hg
    simpa only [d259108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29560 (p : Pattern) (guard : d259109 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259106 p = 1 := by simpa only [d259109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29557 p hg
    simpa only [d259109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259108 p = 1 := by simpa only [d259109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29559 p hg
    simpa only [d259109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29561 (p : Pattern) (guard : d259110 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259109 p = 1 := by simpa only [d259110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29560 p hg
    simpa only [d259110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29562 (p : Pattern) (guard : d259111 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259110 p = 1 := by simpa only [d259111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29561 p hg
    simpa only [d259111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29563 (p : Pattern) (guard : d259112 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259111 p = 1 := by simpa only [d259112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29562 p hg
    simpa only [d259112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29564 (p : Pattern) (guard : d259113 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259078 p = 1 := by simpa only [d259113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29529 p hg
    simpa only [d259113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29565 (p : Pattern) (guard : d259114 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259113 p = 1 := by simpa only [d259114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29564 p hg
    simpa only [d259114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29566 (p : Pattern) (guard : d259115 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259114 p = 1 := by simpa only [d259115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29565 p hg
    simpa only [d259115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29567 (p : Pattern) (guard : d259116 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259082 p = 1 := by simpa only [d259116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29533 p hg
    simpa only [d259116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29568 (p : Pattern) (guard : d259117 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259116 p = 1 := by simpa only [d259117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29567 p hg
    simpa only [d259117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29569 (p : Pattern) (guard : d259118 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259117 p = 1 := by simpa only [d259118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29568 p hg
    simpa only [d259118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29570 (p : Pattern) (guard : d259119 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259115 p = 1 := by simpa only [d259119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29566 p hg
    simpa only [d259119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259118 p = 1 := by simpa only [d259119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29569 p hg
    simpa only [d259119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29571 (p : Pattern) (guard : d259120 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259119 p = 1 := by simpa only [d259120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29570 p hg
    simpa only [d259120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29572 (p : Pattern) (guard : d259121 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259120 p = 1 := by simpa only [d259121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29571 p hg
    simpa only [d259121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29573 (p : Pattern) (guard : d1999 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29305 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29574 (p : Pattern) (guard : d2000 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29573 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29575 (p : Pattern) (guard : d30077 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29574 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29576 (p : Pattern) (guard : d30078 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29575 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29577 (p : Pattern) (guard : d257870 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29576 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29578 (p : Pattern) (guard : d2013 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29120 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29579 (p : Pattern) (guard : d2014 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29305 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29578 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29580 (p : Pattern) (guard : d257871 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29579 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29581 (p : Pattern) (guard : d257872 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29580 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29582 (p : Pattern) (guard : d257873 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29581 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29583 (p : Pattern) (guard : d257874 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29582 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29584 (p : Pattern) (guard : d257875 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29577 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29583 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29585 (p : Pattern) (guard : d257876 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29584 p hg
    simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29586 (p : Pattern) (guard : d259122 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29310 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29587 (p : Pattern) (guard : d259123 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259122 p = 1 := by simpa only [d259123, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29586 p hg
    simpa only [d259123, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259123, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d259123, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29588 (p : Pattern) (guard : d259124 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29585 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259123 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29587 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29589 (p : Pattern) (guard : d259125 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259124 p = 1 := by simpa only [d259125, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29588 p hg
    simpa only [d259125, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259125, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259125, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29590 (p : Pattern) (guard : d259126 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259125 p = 1 := by simpa only [d259126, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29589 p hg
    simpa only [d259126, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259126, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259126, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29591 (p : Pattern) (guard : d259127 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259127, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259127, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259126 p = 1 := by simpa only [d259127, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29590 p hg
    simpa only [d259127, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29592 (p : Pattern) (guard : d259128 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259127 p = 1 := by simpa only [d259128, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29591 p hg
    simpa only [d259128, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259128, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259128, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29593 (p : Pattern) (guard : d259129 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259128 p = 1 := by simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29592 p hg
    simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258946 p = 1 := by simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29319 p hg
    simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29594 (p : Pattern) (guard : d259130 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259123 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29587 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29314 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29595 (p : Pattern) (guard : d259131 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259130 p = 1 := by simpa only [d259131, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29594 p hg
    simpa only [d259131, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259131, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259131, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29596 (p : Pattern) (guard : d259132 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259131 p = 1 := by simpa only [d259132, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29595 p hg
    simpa only [d259132, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259132, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259132, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29597 (p : Pattern) (guard : d259133 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259133, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259133, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259132 p = 1 := by simpa only [d259133, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29596 p hg
    simpa only [d259133, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29598 (p : Pattern) (guard : d259134 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259133 p = 1 := by simpa only [d259134, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29597 p hg
    simpa only [d259134, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259134, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259134, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29599 (p : Pattern) (guard : d259135 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259134 p = 1 := by simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29598 p hg
    simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258952 p = 1 := by simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29600 (p : Pattern) (guard : d259136 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259129 p = 1 := by simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29593 p hg
    simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259135 p = 1 := by simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29599 p hg
    simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29601 (p : Pattern) (guard : d259137 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259136 p = 1 := by simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29600 p hg
    simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258954 p = 1 := by simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29327 p hg
    simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29602 (p : Pattern) (guard : d259138 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259138, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259138, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259137 p = 1 := by simpa only [d259138, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29601 p hg
    simpa only [d259138, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29603 (p : Pattern) (guard : d259139 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259139, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259139, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259138 p = 1 := by simpa only [d259139, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29602 p hg
    simpa only [d259139, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29604 (p : Pattern) (guard : d259140 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258953 p = 1 := by simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29326 p hg
    simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258706 p = 1 := by simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28923 p hg
    simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29605 (p : Pattern) (guard : d259141 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258954 p = 1 := by simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29327 p hg
    simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259140 p = 1 := by simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29604 p hg
    simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29606 (p : Pattern) (guard : d259142 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259142, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259142, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259141 p = 1 := by simpa only [d259142, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29605 p hg
    simpa only [d259142, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29607 (p : Pattern) (guard : d259143 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259143, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259143, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259142 p = 1 := by simpa only [d259143, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29606 p hg
    simpa only [d259143, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29608 (p : Pattern) (guard : d259144 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259139 p = 1 := by simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29603 p hg
    simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259143 p = 1 := by simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29607 p hg
    simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29609 (p : Pattern) (guard : d259145 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259144 p = 1 := by simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29608 p hg
    simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258958 p = 1 := by simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29331 p hg
    simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29610 (p : Pattern) (guard : d259146 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259145 p = 1 := by simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29609 p hg
    simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29611 (p : Pattern) (guard : d259147 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259146 p = 1 := by simpa only [d259147, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29610 p hg
    simpa only [d259147, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259147, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259147, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29612 (p : Pattern) (guard : d259148 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259148, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259148, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259147 p = 1 := by simpa only [d259148, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29611 p hg
    simpa only [d259148, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29613 (p : Pattern) (guard : d259149 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259148 p = 1 := by simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29612 p hg
    simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259073 p = 1 := by simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29524 p hg
    simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29614 (p : Pattern) (guard : d259150 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259149 p = 1 := by simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29613 p hg
    simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29615 (p : Pattern) (guard : d259151 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259150 p = 1 := by simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29614 p hg
    simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29616 (p : Pattern) (guard : d259152 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259151 p = 1 := by simpa only [d259152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29615 p hg
    simpa only [d259152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29617 (p : Pattern) (guard : d259153 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259152 p = 1 := by simpa only [d259153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29616 p hg
    simpa only [d259153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259081 p = 1 := by simpa only [d259153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29532 p hg
    simpa only [d259153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29618 (p : Pattern) (guard : d259154 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259153 p = 1 := by simpa only [d259154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29617 p hg
    simpa only [d259154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29619 (p : Pattern) (guard : d259155 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259073 p = 1 := by simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29524 p hg
    simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29620 (p : Pattern) (guard : d259156 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259155 p = 1 := by simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29619 p hg
    simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29621 (p : Pattern) (guard : d259157 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259156 p = 1 := by simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29620 p hg
    simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29622 (p : Pattern) (guard : d259158 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259157 p = 1 := by simpa only [d259158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29621 p hg
    simpa only [d259158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29623 (p : Pattern) (guard : d259159 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259158 p = 1 := by simpa only [d259159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29622 p hg
    simpa only [d259159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29624 (p : Pattern) (guard : d259160 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259159 p = 1 := by simpa only [d259160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29623 p hg
    simpa only [d259160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29625 (p : Pattern) (guard : d259161 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259154 p = 1 := by simpa only [d259161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29618 p hg
    simpa only [d259161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259160 p = 1 := by simpa only [d259161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29624 p hg
    simpa only [d259161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29626 (p : Pattern) (guard : d259162 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d259121 p = 1 := by simpa only [d259162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29572 p hg
    simpa only [d259162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259161 p = 1 := by simpa only [d259162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29625 p hg
    simpa only [d259162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29627 (p : Pattern) (guard : d259163 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d259112 p = 1 := by simpa only [d259163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29563 p hg
    simpa only [d259163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259162 p = 1 := by simpa only [d259163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29626 p hg
    simpa only [d259163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29628 (p : Pattern) (guard : d259164 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259163 p = 1 := by simpa only [d259164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29627 p hg
    simpa only [d259164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29629 (p : Pattern) (guard : d259165 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259105 p = 1 := by simpa only [d259165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29556 p hg
    simpa only [d259165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29630 (p : Pattern) (guard : d259166 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259107 p = 1 := by simpa only [d259166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29558 p hg
    simpa only [d259166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29631 (p : Pattern) (guard : d259167 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259165 p = 1 := by simpa only [d259167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29629 p hg
    simpa only [d259167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259166 p = 1 := by simpa only [d259167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29630 p hg
    simpa only [d259167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29632 (p : Pattern) (guard : d259168 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259167 p = 1 := by simpa only [d259168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29631 p hg
    simpa only [d259168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29633 (p : Pattern) (guard : d259169 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259168 p = 1 := by simpa only [d259169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29632 p hg
    simpa only [d259169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29634 (p : Pattern) (guard : d259170 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259169 p = 1 := by simpa only [d259170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29633 p hg
    simpa only [d259170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29635 (p : Pattern) (guard : d259171 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259114 p = 1 := by simpa only [d259171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29565 p hg
    simpa only [d259171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29636 (p : Pattern) (guard : d259172 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259117 p = 1 := by simpa only [d259172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29568 p hg
    simpa only [d259172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29637 (p : Pattern) (guard : d259173 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259171 p = 1 := by simpa only [d259173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29635 p hg
    simpa only [d259173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259172 p = 1 := by simpa only [d259173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29636 p hg
    simpa only [d259173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29638 (p : Pattern) (guard : d259174 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259173 p = 1 := by simpa only [d259174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29637 p hg
    simpa only [d259174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29639 (p : Pattern) (guard : d259175 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259174 p = 1 := by simpa only [d259175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29638 p hg
    simpa only [d259175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29640 (p : Pattern) (guard : d259176 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259151 p = 1 := by simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29615 p hg
    simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29641 (p : Pattern) (guard : d259177 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259176 p = 1 := by simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29640 p hg
    simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259094 p = 1 := by simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29545 p hg
    simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29642 (p : Pattern) (guard : d259178 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259177 p = 1 := by simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29641 p hg
    simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29643 (p : Pattern) (guard : d259179 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259157 p = 1 := by simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29621 p hg
    simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29644 (p : Pattern) (guard : d259180 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259179 p = 1 := by simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29643 p hg
    simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29645 (p : Pattern) (guard : d259181 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259180 p = 1 := by simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29644 p hg
    simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29646 (p : Pattern) (guard : d259182 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259178 p = 1 := by simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29642 p hg
    simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259181 p = 1 := by simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29645 p hg
    simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29647 (p : Pattern) (guard : d259183 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d259175 p = 1 := by simpa only [d259183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29639 p hg
    simpa only [d259183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259182 p = 1 := by simpa only [d259183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29646 p hg
    simpa only [d259183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29648 (p : Pattern) (guard : d259184 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d259170 p = 1 := by simpa only [d259184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29634 p hg
    simpa only [d259184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259183 p = 1 := by simpa only [d259184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29647 p hg
    simpa only [d259184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29649 (p : Pattern) (guard : d259185 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259163 p = 1 := by simpa only [d259185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29627 p hg
    simpa only [d259185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259184 p = 1 := by simpa only [d259185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29648 p hg
    simpa only [d259185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29650 (p : Pattern) (guard : d259186 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259164 p = 1 := by simpa only [d259186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29628 p hg
    simpa only [d259186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259185 p = 1 := by simpa only [d259186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29649 p hg
    simpa only [d259186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29651 (p : Pattern) (guard : d259187 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259085 p = 1 := by simpa only [d259187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29536 p hg
    simpa only [d259187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29652 (p : Pattern) (guard : d259188 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259187 p = 1 := by simpa only [d259188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29651 p hg
    simpa only [d259188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29653 (p : Pattern) (guard : d259189 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259188 p = 1 := by simpa only [d259189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29652 p hg
    simpa only [d259189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29654 (p : Pattern) (guard : d259190 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259189 p = 1 := by simpa only [d259190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29653 p hg
    simpa only [d259190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29655 (p : Pattern) (guard : d259191 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259190 p = 1 := by simpa only [d259191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29654 p hg
    simpa only [d259191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29656 (p : Pattern) (guard : d259192 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259090 p = 1 := by simpa only [d259192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29541 p hg
    simpa only [d259192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259191 p = 1 := by simpa only [d259192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29655 p hg
    simpa only [d259192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29657 (p : Pattern) (guard : d259193 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259095 p = 1 := by simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29546 p hg
    simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29658 (p : Pattern) (guard : d259194 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259193 p = 1 := by simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29657 p hg
    simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29659 (p : Pattern) (guard : d259195 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259194 p = 1 := by simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29658 p hg
    simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29660 (p : Pattern) (guard : d259196 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259195 p = 1 := by simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29659 p hg
    simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29661 (p : Pattern) (guard : d259197 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259196 p = 1 := by simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29660 p hg
    simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29662 (p : Pattern) (guard : d259198 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259191 p = 1 := by simpa only [d259198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29655 p hg
    simpa only [d259198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259197 p = 1 := by simpa only [d259198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29661 p hg
    simpa only [d259198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29663 (p : Pattern) (guard : d259199 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259192 p = 1 := by simpa only [d259199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29656 p hg
    simpa only [d259199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259198 p = 1 := by simpa only [d259199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29662 p hg
    simpa only [d259199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29664 (p : Pattern) (guard : d259200 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259186 p = 1 := by simpa only [d259200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29650 p hg
    simpa only [d259200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259199 p = 1 := by simpa only [d259200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29663 p hg
    simpa only [d259200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29665 (p : Pattern) (guard : d259201 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259200 p = 1 := by simpa only [d259201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29664 p hg
    simpa only [d259201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29666 (p : Pattern) (guard : d259202 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259104 p = 1 := by simpa only [d259202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29555 p hg
    simpa only [d259202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259201 p = 1 := by simpa only [d259202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29665 p hg
    simpa only [d259202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29667 (p : Pattern) (guard : d1999 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29377 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29668 (p : Pattern) (guard : d2000 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29667 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29669 (p : Pattern) (guard : d30077 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29668 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29670 (p : Pattern) (guard : d30078 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29669 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29671 (p : Pattern) (guard : d257870 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29670 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29672 (p : Pattern) (guard : d2013 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29177 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29673 (p : Pattern) (guard : d2014 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29377 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29672 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29674 (p : Pattern) (guard : d257871 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29673 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29675 (p : Pattern) (guard : d257872 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29674 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29676 (p : Pattern) (guard : d257873 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29675 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29677 (p : Pattern) (guard : d257874 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29676 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29678 (p : Pattern) (guard : d257875 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29671 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29677 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29679 (p : Pattern) (guard : d257876 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29678 p hg
    simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29680 (p : Pattern) (guard : d259122 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29382 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29681 (p : Pattern) (guard : d259123 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259122 p = 1 := by simpa only [d259123, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29680 p hg
    simpa only [d259123, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259123, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d259123, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29682 (p : Pattern) (guard : d259124 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29679 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259123 p = 1 := by simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29681 p hg
    simpa only [d259124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29683 (p : Pattern) (guard : d259125 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259124 p = 1 := by simpa only [d259125, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29682 p hg
    simpa only [d259125, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259125, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259125, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29684 (p : Pattern) (guard : d259126 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259125 p = 1 := by simpa only [d259126, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29683 p hg
    simpa only [d259126, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259126, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259126, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29685 (p : Pattern) (guard : d259127 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259127, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259127, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259126 p = 1 := by simpa only [d259127, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29684 p hg
    simpa only [d259127, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29686 (p : Pattern) (guard : d259128 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259127 p = 1 := by simpa only [d259128, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29685 p hg
    simpa only [d259128, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259128, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259128, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29687 (p : Pattern) (guard : d259129 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259128 p = 1 := by simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29686 p hg
    simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258946 p = 1 := by simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29391 p hg
    simpa only [d259129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29688 (p : Pattern) (guard : d259130 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259123 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29681 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29386 p hg
    simpa only [d259130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29689 (p : Pattern) (guard : d259131 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259130 p = 1 := by simpa only [d259131, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29688 p hg
    simpa only [d259131, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259131, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259131, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29690 (p : Pattern) (guard : d259132 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259131 p = 1 := by simpa only [d259132, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29689 p hg
    simpa only [d259132, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259132, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259132, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29691 (p : Pattern) (guard : d259133 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259133, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259133, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259132 p = 1 := by simpa only [d259133, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29690 p hg
    simpa only [d259133, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29692 (p : Pattern) (guard : d259134 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259133 p = 1 := by simpa only [d259134, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29691 p hg
    simpa only [d259134, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259134, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259134, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29693 (p : Pattern) (guard : d259135 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259134 p = 1 := by simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29692 p hg
    simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258952 p = 1 := by simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29397 p hg
    simpa only [d259135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29694 (p : Pattern) (guard : d259136 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259129 p = 1 := by simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29687 p hg
    simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259135 p = 1 := by simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29693 p hg
    simpa only [d259136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29695 (p : Pattern) (guard : d259137 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259136 p = 1 := by simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29694 p hg
    simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258954 p = 1 := by simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29399 p hg
    simpa only [d259137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29696 (p : Pattern) (guard : d259138 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259138, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259138, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259137 p = 1 := by simpa only [d259138, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29695 p hg
    simpa only [d259138, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29697 (p : Pattern) (guard : d259139 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259139, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259139, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259138 p = 1 := by simpa only [d259139, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29696 p hg
    simpa only [d259139, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29698 (p : Pattern) (guard : d259140 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258953 p = 1 := by simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29398 p hg
    simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258706 p = 1 := by simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28985 p hg
    simpa only [d259140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29699 (p : Pattern) (guard : d259141 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258954 p = 1 := by simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29399 p hg
    simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259140 p = 1 := by simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29698 p hg
    simpa only [d259141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29700 (p : Pattern) (guard : d259142 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259142, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259142, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259141 p = 1 := by simpa only [d259142, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29699 p hg
    simpa only [d259142, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29701 (p : Pattern) (guard : d259143 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259143, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259143, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259142 p = 1 := by simpa only [d259143, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29700 p hg
    simpa only [d259143, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29702 (p : Pattern) (guard : d259144 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259139 p = 1 := by simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29697 p hg
    simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259143 p = 1 := by simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29701 p hg
    simpa only [d259144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29703 (p : Pattern) (guard : d259145 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259144 p = 1 := by simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29702 p hg
    simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258958 p = 1 := by simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29403 p hg
    simpa only [d259145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29704 (p : Pattern) (guard : d259146 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259145 p = 1 := by simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29703 p hg
    simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29705 (p : Pattern) (guard : d259147 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259146 p = 1 := by simpa only [d259147, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29704 p hg
    simpa only [d259147, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259147, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259147, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29706 (p : Pattern) (guard : d259148 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259148, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259148, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259147 p = 1 := by simpa only [d259148, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29705 p hg
    simpa only [d259148, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29707 (p : Pattern) (guard : d259069 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29195 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29708 (p : Pattern) (guard : d259070 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258958 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29403 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259069 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29707 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29709 (p : Pattern) (guard : d259071 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259070 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29708 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29710 (p : Pattern) (guard : d259072 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259071 p = 1 := by simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29709 p hg
    simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29711 (p : Pattern) (guard : d259073 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259072 p = 1 := by simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29710 p hg
    simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29712 (p : Pattern) (guard : d259149 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259148 p = 1 := by simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29706 p hg
    simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259073 p = 1 := by simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29711 p hg
    simpa only [d259149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29713 (p : Pattern) (guard : d259150 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259149 p = 1 := by simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29712 p hg
    simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29714 (p : Pattern) (guard : d259151 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259150 p = 1 := by simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29713 p hg
    simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29715 (p : Pattern) (guard : d259176 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259151 p = 1 := by simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29714 p hg
    simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29716 (p : Pattern) (guard : d259074 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259069 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29707 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29717 (p : Pattern) (guard : d259075 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259074 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29716 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29718 (p : Pattern) (guard : d259076 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259075 p = 1 := by simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29717 p hg
    simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29719 (p : Pattern) (guard : d259077 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259076 p = 1 := by simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29718 p hg
    simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29720 (p : Pattern) (guard : d259078 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259073 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29711 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259077 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29719 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29721 (p : Pattern) (guard : d259079 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259078 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29720 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29722 (p : Pattern) (guard : d259080 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259079 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29721 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29723 (p : Pattern) (guard : d259094 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259080 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29722 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29724 (p : Pattern) (guard : d259177 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259176 p = 1 := by simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29715 p hg
    simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259094 p = 1 := by simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29723 p hg
    simpa only [d259177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29725 (p : Pattern) (guard : d259178 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259177 p = 1 := by simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29724 p hg
    simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29726 (p : Pattern) (guard : d259155 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259073 p = 1 := by simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29711 p hg
    simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29727 (p : Pattern) (guard : d259156 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259155 p = 1 := by simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29726 p hg
    simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29728 (p : Pattern) (guard : d259157 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259156 p = 1 := by simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29727 p hg
    simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29729 (p : Pattern) (guard : d259179 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259157 p = 1 := by simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29728 p hg
    simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29730 (p : Pattern) (guard : d259180 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259179 p = 1 := by simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29729 p hg
    simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29731 (p : Pattern) (guard : d259181 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259180 p = 1 := by simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29730 p hg
    simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29732 (p : Pattern) (guard : d259182 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259178 p = 1 := by simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29725 p hg
    simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259181 p = 1 := by simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29731 p hg
    simpa only [d259182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29733 (p : Pattern) (guard : d259203 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259182 p = 1 := by simpa only [d259203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29732 p hg
    simpa only [d259203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29734 (p : Pattern) (guard : d259204 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259203 p = 1 := by simpa only [d259204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29733 p hg
    simpa only [d259204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29735 (p : Pattern) (guard : d259205 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259205, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259205, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259204 p = 1 := by simpa only [d259205, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29734 p hg
    simpa only [d259205, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29736 (p : Pattern) (guard : d259206 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259205 p = 1 := by simpa only [d259206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29735 p hg
    simpa only [d259206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29737 (p : Pattern) (guard : d259082 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259077 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29719 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29738 (p : Pattern) (guard : d259083 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259082 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29737 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29739 (p : Pattern) (guard : d259084 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259083 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29738 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29740 (p : Pattern) (guard : d259095 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259084 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29739 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29741 (p : Pattern) (guard : d259193 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259095 p = 1 := by simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29740 p hg
    simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29742 (p : Pattern) (guard : d259194 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259193 p = 1 := by simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29741 p hg
    simpa only [d259194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29743 (p : Pattern) (guard : d259195 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259194 p = 1 := by simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29742 p hg
    simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29744 (p : Pattern) (guard : d259196 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259195 p = 1 := by simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29743 p hg
    simpa only [d259196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29745 (p : Pattern) (guard : d259197 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259196 p = 1 := by simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29744 p hg
    simpa only [d259197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29746 (p : Pattern) (guard : d259207 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259207, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259207, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259197 p = 1 := by simpa only [d259207, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29745 p hg
    simpa only [d259207, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29747 (p : Pattern) (guard : d259208 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259207 p = 1 := by simpa only [d259208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29746 p hg
    simpa only [d259208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29748 (p : Pattern) (guard : d259209 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259206 p = 1 := by simpa only [d259209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29736 p hg
    simpa only [d259209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259208 p = 1 := by simpa only [d259209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29747 p hg
    simpa only [d259209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29749 (p : Pattern) (guard : d259210 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259209 p = 1 := by simpa only [d259210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29748 p hg
    simpa only [d259210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259210, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
