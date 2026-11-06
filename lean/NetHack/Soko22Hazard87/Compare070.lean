import NetHack.Soko22Hazard87.Compare069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17500 (p : Pattern) (guard : d15390 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15389 p = 1 := by simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17499 p hg
    simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d15390, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17501 (p : Pattern) (guard : d15399 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17502 (p : Pattern) (guard : d15400 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15399 p = 1 := by simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17501 p hg
    simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d15400, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17503 (p : Pattern) (guard : d17016 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15390 p = 1 := by simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17500 p hg
    simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15400 p = 1 := by simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17502 p hg
    simpa only [d17016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17504 (p : Pattern) (guard : d17017 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17015 p = 1 := by simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17498 p hg
    simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17016 p = 1 := by simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17503 p hg
    simpa only [d17017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17505 (p : Pattern) (guard : d1864 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17506 (p : Pattern) (guard : d1865 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1864 p = 1 := by simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17505 p hg
    simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d1865, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17507 (p : Pattern) (guard : d17029 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17508 (p : Pattern) (guard : d17030 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17029 p = 1 := by simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17507 p hg
    simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d17030, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17509 (p : Pattern) (guard : d17031 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1865 p = 1 := by simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17506 p hg
    simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17030 p = 1 := by simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17508 p hg
    simpa only [d17031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17510 (p : Pattern) (guard : d15401 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15400 p = 1 := by simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17502 p hg
    simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d15401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17511 (p : Pattern) (guard : d17032 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17031 p = 1 := by simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17509 p hg
    simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15401 p = 1 := by simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17510 p hg
    simpa only [d17032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17512 (p : Pattern) (guard : d17033 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17017 p = 1 := by simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17504 p hg
    simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17032 p = 1 := by simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17511 p hg
    simpa only [d17033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17513 (p : Pattern) (guard : d17034 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17033 p = 1 := by simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17512 p hg
    simpa only [d17034, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17514 (p : Pattern) (guard : d17035 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17034 p = 1 := by simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17513 p hg
    simpa only [d17035, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17515 (p : Pattern) (guard : d6498 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17516 (p : Pattern) (guard : d6499 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6498 p = 1 := by simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17515 p hg
    simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d6499, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17517 (p : Pattern) (guard : d6500 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6499 p = 1 := by simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17516 p hg
    simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17518 (p : Pattern) (guard : d15414 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17519 (p : Pattern) (guard : d15415 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15414 p = 1 := by simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17518 p hg
    simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d15415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17520 (p : Pattern) (guard : d15416 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15415 p = 1 := by simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17519 p hg
    simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d15416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17521 (p : Pattern) (guard : d15417 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6500 p = 1 := by simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17517 p hg
    simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15416 p = 1 := by simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17520 p hg
    simpa only [d15417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17522 (p : Pattern) (guard : d17036 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17032 p = 1 := by simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17511 p hg
    simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15417 p = 1 := by simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17521 p hg
    simpa only [d17036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17523 (p : Pattern) (guard : d17037 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17036 p = 1 := by simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17522 p hg
    simpa only [d17037, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17524 (p : Pattern) (guard : d17038 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17037 p = 1 := by simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17523 p hg
    simpa only [d17038, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17525 (p : Pattern) (guard : d17039 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17035 p = 1 := by simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17514 p hg
    simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17038 p = 1 := by simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17524 p hg
    simpa only [d17039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17526 (p : Pattern) (guard : d1870 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17527 (p : Pattern) (guard : d1871 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1870 p = 1 := by simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17526 p hg
    simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d1871, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17528 (p : Pattern) (guard : d1877 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1871 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17527 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17529 (p : Pattern) (guard : d15435 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1877 p = 1 := by simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17528 p hg
    simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15416 p = 1 := by simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17520 p hg
    simpa only [d15435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17530 (p : Pattern) (guard : d17053 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17032 p = 1 := by simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17511 p hg
    simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15435 p = 1 := by simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17529 p hg
    simpa only [d17053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17531 (p : Pattern) (guard : d17054 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17053 p = 1 := by simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17530 p hg
    simpa only [d17054, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17532 (p : Pattern) (guard : d17055 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17054 p = 1 := by simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17531 p hg
    simpa only [d17055, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17533 (p : Pattern) (guard : d17056 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17055 p = 1 := by simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17532 p hg
    simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d17056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17534 (p : Pattern) (guard : d171176 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17039 p = 1 := by simpa only [d171176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17525 p hg
    simpa only [d171176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17056 p = 1 := by simpa only [d171176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17533 p hg
    simpa only [d171176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17535 (p : Pattern) (guard : d171177 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d171176 p = 1 := by simpa only [d171177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17534 p hg
    simpa only [d171177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d171177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17536 (p : Pattern) (guard : d171178 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d171177 p = 1 := by simpa only [d171178, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17535 p hg
    simpa only [d171178, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171178, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d171178, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17537 (p : Pattern) (guard : d171179 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171179, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d171179, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171178 p = 1 := by simpa only [d171179, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17536 p hg
    simpa only [d171179, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17538 (p : Pattern) (guard : d17057 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17056 p = 1 := by simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17533 p hg
    simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d17057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17539 (p : Pattern) (guard : d17058 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17057 p = 1 := by simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17538 p hg
    simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d17058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17540 (p : Pattern) (guard : d17059 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17058 p = 1 := by simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17539 p hg
    simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d17059, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17541 (p : Pattern) (guard : d17060 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17059 p = 1 := by simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17540 p hg
    simpa only [d17060, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17542 (p : Pattern) (guard : d171180 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d171179 p = 1 := by simpa only [d171180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17537 p hg
    simpa only [d171180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17060 p = 1 := by simpa only [d171180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17541 p hg
    simpa only [d171180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17543 (p : Pattern) (guard : d171181 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d171180 p = 1 := by simpa only [d171181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17542 p hg
    simpa only [d171181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17544 (p : Pattern) (guard : d171182 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d171181 p = 1 := by simpa only [d171182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17543 p hg
    simpa only [d171182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17545 (p : Pattern) (guard : d171183 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d171182 p = 1 := by simpa only [d171183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17544 p hg
    simpa only [d171183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17546 (p : Pattern) (guard : d17127 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17060 p = 1 := by simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17541 p hg
    simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17547 (p : Pattern) (guard : d17128 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17127 p = 1 := by simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17546 p hg
    simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17548 (p : Pattern) (guard : d17129 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17128 p = 1 := by simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17547 p hg
    simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17549 (p : Pattern) (guard : d17130 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17129 p = 1 := by simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17548 p hg
    simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17550 (p : Pattern) (guard : d171184 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d171183 p = 1 := by simpa only [d171184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17545 p hg
    simpa only [d171184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17130 p = 1 := by simpa only [d171184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17549 p hg
    simpa only [d171184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17551 (p : Pattern) (guard : d171185 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171184 p = 1 := by simpa only [d171185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17550 p hg
    simpa only [d171185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17552 (p : Pattern) (guard : d171186 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d171185 p = 1 := by simpa only [d171186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17551 p hg
    simpa only [d171186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17553 (p : Pattern) (guard : d171187 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171186 p = 1 := by simpa only [d171187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17552 p hg
    simpa only [d171187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17554 (p : Pattern) (guard : d171188 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171187 p = 1 := by simpa only [d171188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17553 p hg
    simpa only [d171188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17555 (p : Pattern) (guard : d171189 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171189, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171189, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171188 p = 1 := by simpa only [d171189, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17554 p hg
    simpa only [d171189, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17556 (p : Pattern) (guard : d171190 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171189 p = 1 := by simpa only [d171190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17555 p hg
    simpa only [d171190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17557 (p : Pattern) (guard : d171191 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171190 p = 1 := by simpa only [d171191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17556 p hg
    simpa only [d171191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17558 (p : Pattern) (guard : d171192 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171191 p = 1 := by simpa only [d171192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17557 p hg
    simpa only [d171192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17559 (p : Pattern) (guard : d171193 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171192 p = 1 := by simpa only [d171193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17558 p hg
    simpa only [d171193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17560 (p : Pattern) (guard : d171194 p = 1) : d48387 p ≤ (0 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171193 p = 1 := by simpa only [d171194, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17559 p hg
    simpa only [d171194, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171194, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d171194, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17561 (p : Pattern) (guard : d171195 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171175 p = 1 := by simpa only [d171195, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17493 p hg
    simpa only [d171195, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171194 p = 1 := by simpa only [d171195, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17560 p hg
    simpa only [d171195, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17562 (p : Pattern) (guard : d171196 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171195 p = 1 := by simpa only [d171196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17561 p hg
    simpa only [d171196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17563 (p : Pattern) (guard : d171197 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171196 p = 1 := by simpa only [d171197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17562 p hg
    simpa only [d171197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17564 (p : Pattern) (guard : d171198 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171197 p = 1 := by simpa only [d171198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17563 p hg
    simpa only [d171198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17565 (p : Pattern) (guard : d171199 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171198 p = 1 := by simpa only [d171199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17564 p hg
    simpa only [d171199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17566 (p : Pattern) (guard : d171200 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171199 p = 1 := by simpa only [d171200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17565 p hg
    simpa only [d171200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17567 (p : Pattern) (guard : d171201 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171200 p = 1 := by simpa only [d171201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17566 p hg
    simpa only [d171201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17568 (p : Pattern) (guard : d171202 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171201 p = 1 := by simpa only [d171202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17567 p hg
    simpa only [d171202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17569 (p : Pattern) (guard : d171203 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171202 p = 1 := by simpa only [d171203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17568 p hg
    simpa only [d171203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17570 (p : Pattern) (guard : d171204 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171203 p = 1 := by simpa only [d171204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17569 p hg
    simpa only [d171204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17571 (p : Pattern) (guard : d171205 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d171167 p = 1 := by simpa only [d171205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17326 p hg
    simpa only [d171205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171204 p = 1 := by simpa only [d171205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17570 p hg
    simpa only [d171205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17572 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17573 (p : Pattern) (guard : d2038 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17572 p hg
    simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d2038, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17574 (p : Pattern) (guard : d17153 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17575 (p : Pattern) (guard : d17154 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17574 p hg
    simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d17154, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17576 (p : Pattern) (guard : d17155 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17573 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17575 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17577 (p : Pattern) (guard : d13675 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17578 (p : Pattern) (guard : d13676 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17577 p hg
    simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d13676, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17579 (p : Pattern) (guard : d15548 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17580 (p : Pattern) (guard : d15549 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17579 p hg
    simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d15549, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17581 (p : Pattern) (guard : d17156 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17578 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17580 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17582 (p : Pattern) (guard : d17157 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17576 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17581 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17583 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17584 (p : Pattern) (guard : d2056 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17583 p hg
    simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d2056, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17585 (p : Pattern) (guard : d17158 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17586 (p : Pattern) (guard : d17159 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17585 p hg
    simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d17159, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17587 (p : Pattern) (guard : d17160 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17584 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17586 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17588 (p : Pattern) (guard : d15550 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17580 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17589 (p : Pattern) (guard : d17161 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17587 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17588 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17590 (p : Pattern) (guard : d17162 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17582 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17589 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17591 (p : Pattern) (guard : d17163 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17590 p hg
    simpa only [d17163, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17592 (p : Pattern) (guard : d17164 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17591 p hg
    simpa only [d17164, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17593 (p : Pattern) (guard : d5249 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17594 (p : Pattern) (guard : d5250 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17593 p hg
    simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d5250, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17595 (p : Pattern) (guard : d5251 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17594 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17596 (p : Pattern) (guard : d15555 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17597 (p : Pattern) (guard : d15556 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17596 p hg
    simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d15556, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17598 (p : Pattern) (guard : d15557 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17597 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17599 (p : Pattern) (guard : d15558 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17595 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17598 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17600 (p : Pattern) (guard : d17165 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17589 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17599 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17601 (p : Pattern) (guard : d17166 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17600 p hg
    simpa only [d17166, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17602 (p : Pattern) (guard : d17167 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17601 p hg
    simpa only [d17167, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17603 (p : Pattern) (guard : d17168 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17592 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17602 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17604 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17605 (p : Pattern) (guard : d2068 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17604 p hg
    simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d2068, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17606 (p : Pattern) (guard : d2071 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17605 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17607 (p : Pattern) (guard : d15563 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17606 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17598 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17608 (p : Pattern) (guard : d17169 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17589 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17607 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17609 (p : Pattern) (guard : d17170 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17608 p hg
    simpa only [d17170, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17610 (p : Pattern) (guard : d17171 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17609 p hg
    simpa only [d17171, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17611 (p : Pattern) (guard : d17172 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17610 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17612 (p : Pattern) (guard : d17173 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17603 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17611 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17613 (p : Pattern) (guard : d17174 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17612 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17614 (p : Pattern) (guard : d17175 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17613 p hg
    simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d17175, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17615 (p : Pattern) (guard : d17176 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17614 p hg
    simpa only [d17176, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17616 (p : Pattern) (guard : d17177 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17611 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17617 (p : Pattern) (guard : d17178 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17616 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17618 (p : Pattern) (guard : d17179 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17617 p hg
    simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d17179, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17619 (p : Pattern) (guard : d17180 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17618 p hg
    simpa only [d17180, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17620 (p : Pattern) (guard : d17181 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17615 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17619 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17621 (p : Pattern) (guard : d17182 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17620 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17622 (p : Pattern) (guard : d17183 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17621 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17623 (p : Pattern) (guard : d17184 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17622 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17624 (p : Pattern) (guard : d17185 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17619 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17625 (p : Pattern) (guard : d17186 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17624 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17626 (p : Pattern) (guard : d17187 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17625 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17627 (p : Pattern) (guard : d17188 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17626 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17628 (p : Pattern) (guard : d17189 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17623 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17627 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17629 (p : Pattern) (guard : d17190 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17628 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17630 (p : Pattern) (guard : d17191 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17629 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17631 (p : Pattern) (guard : d17192 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17630 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17632 (p : Pattern) (guard : d17193 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17631 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17633 (p : Pattern) (guard : d17194 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17193 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17632 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17634 (p : Pattern) (guard : d17164 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17591 p hg
    simpa only [d17164, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17635 (p : Pattern) (guard : d17167 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17601 p hg
    simpa only [d17167, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17636 (p : Pattern) (guard : d17168 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17634 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17635 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17637 (p : Pattern) (guard : d17171 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17609 p hg
    simpa only [d17171, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17638 (p : Pattern) (guard : d17172 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17637 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17639 (p : Pattern) (guard : d17173 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17636 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17638 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17640 (p : Pattern) (guard : d17174 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17639 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17641 (p : Pattern) (guard : d17175 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17640 p hg
    simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d17175, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17642 (p : Pattern) (guard : d17176 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17641 p hg
    simpa only [d17176, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17643 (p : Pattern) (guard : d17177 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17638 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17644 (p : Pattern) (guard : d17178 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17643 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17645 (p : Pattern) (guard : d17179 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d17179, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17646 (p : Pattern) (guard : d17180 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17645 p hg
    simpa only [d17180, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17647 (p : Pattern) (guard : d17181 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17642 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17646 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17648 (p : Pattern) (guard : d17182 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17647 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17649 (p : Pattern) (guard : d17183 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17648 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17650 (p : Pattern) (guard : d17184 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17651 (p : Pattern) (guard : d17185 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17646 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17652 (p : Pattern) (guard : d17186 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17651 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17653 (p : Pattern) (guard : d17187 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17652 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17654 (p : Pattern) (guard : d17188 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17653 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17655 (p : Pattern) (guard : d17189 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17650 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17654 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17656 (p : Pattern) (guard : d17190 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17655 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17657 (p : Pattern) (guard : d17191 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17656 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17658 (p : Pattern) (guard : d17192 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17657 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17659 (p : Pattern) (guard : d17193 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17658 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17660 (p : Pattern) (guard : d17197 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17183 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17622 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17661 (p : Pattern) (guard : d17198 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17626 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17662 (p : Pattern) (guard : d17199 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17197 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17198 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17661 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17663 (p : Pattern) (guard : d17200 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17199 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17662 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17664 (p : Pattern) (guard : d17201 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17200 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17663 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17665 (p : Pattern) (guard : d17202 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17201 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17664 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17666 (p : Pattern) (guard : d17203 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17202 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17665 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17667 (p : Pattern) (guard : d17204 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17193 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17659 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17203 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17668 (p : Pattern) (guard : d17205 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d17194 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17633 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17204 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17667 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17669 (p : Pattern) (guard : d17206 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17205 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17668 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17670 (p : Pattern) (guard : d171206 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d17206 p = 1 := by simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17669 p hg
    simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17671 (p : Pattern) (guard : d171207 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171206 p = 1 := by simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17670 p hg
    simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17672 (p : Pattern) (guard : d2037 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17673 (p : Pattern) (guard : d2038 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17672 p hg
    simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d2038, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17674 (p : Pattern) (guard : d17153 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17675 (p : Pattern) (guard : d17154 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d17154, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17676 (p : Pattern) (guard : d17155 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17675 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17677 (p : Pattern) (guard : d13675 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17678 (p : Pattern) (guard : d13676 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d13676, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17679 (p : Pattern) (guard : d15548 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17680 (p : Pattern) (guard : d15549 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17679 p hg
    simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d15549, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17681 (p : Pattern) (guard : d17156 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17678 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17680 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17682 (p : Pattern) (guard : d17157 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17676 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17681 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17683 (p : Pattern) (guard : d2055 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17684 (p : Pattern) (guard : d2056 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17683 p hg
    simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d2056, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17685 (p : Pattern) (guard : d17158 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17686 (p : Pattern) (guard : d17159 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17685 p hg
    simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d17159, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17687 (p : Pattern) (guard : d17160 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17684 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17686 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17688 (p : Pattern) (guard : d15550 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17680 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17689 (p : Pattern) (guard : d17161 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17687 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17688 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17690 (p : Pattern) (guard : d17162 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17689 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17691 (p : Pattern) (guard : d17163 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17690 p hg
    simpa only [d17163, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17692 (p : Pattern) (guard : d17164 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17691 p hg
    simpa only [d17164, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17693 (p : Pattern) (guard : d5249 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17694 (p : Pattern) (guard : d5250 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17693 p hg
    simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d5250, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17695 (p : Pattern) (guard : d5251 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17694 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17696 (p : Pattern) (guard : d15555 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17697 (p : Pattern) (guard : d15556 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17696 p hg
    simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17698 (p : Pattern) (guard : d15557 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17697 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17699 (p : Pattern) (guard : d15558 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17695 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17698 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17700 (p : Pattern) (guard : d17165 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17689 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17699 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17701 (p : Pattern) (guard : d17166 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17700 p hg
    simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17702 (p : Pattern) (guard : d17167 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17701 p hg
    simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17703 (p : Pattern) (guard : d17168 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17692 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17702 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17704 (p : Pattern) (guard : d2067 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17705 (p : Pattern) (guard : d2068 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17704 p hg
    simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17706 (p : Pattern) (guard : d2071 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17705 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17707 (p : Pattern) (guard : d15563 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17698 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17708 (p : Pattern) (guard : d17169 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17689 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17707 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17709 (p : Pattern) (guard : d17170 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17708 p hg
    simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17710 (p : Pattern) (guard : d17171 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17709 p hg
    simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17711 (p : Pattern) (guard : d17172 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17710 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17712 (p : Pattern) (guard : d17173 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17703 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17713 (p : Pattern) (guard : d17174 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17712 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17714 (p : Pattern) (guard : d17175 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17713 p hg
    simpa only [d17175, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d17175, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17715 (p : Pattern) (guard : d17176 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17714 p hg
    simpa only [d17176, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17716 (p : Pattern) (guard : d17177 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17717 (p : Pattern) (guard : d17178 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17716 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17718 (p : Pattern) (guard : d17179 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17717 p hg
    simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17719 (p : Pattern) (guard : d17180 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17718 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17720 (p : Pattern) (guard : d17181 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17715 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17719 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17721 (p : Pattern) (guard : d17182 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17720 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17722 (p : Pattern) (guard : d17183 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17721 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17723 (p : Pattern) (guard : d17197 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17183 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17722 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17724 (p : Pattern) (guard : d17185 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17719 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17725 (p : Pattern) (guard : d17186 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17724 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17726 (p : Pattern) (guard : d17187 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17725 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17727 (p : Pattern) (guard : d17198 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17726 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17728 (p : Pattern) (guard : d17199 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17197 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17723 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17198 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17727 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17729 (p : Pattern) (guard : d17200 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17199 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17728 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17730 (p : Pattern) (guard : d17201 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17200 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17729 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17731 (p : Pattern) (guard : d17202 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17201 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17730 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17732 (p : Pattern) (guard : d17203 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17202 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17731 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17733 (p : Pattern) (guard : d171208 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171208, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171208, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17203 p = 1 := by simpa only [d171208, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17732 p hg
    simpa only [d171208, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17734 (p : Pattern) (guard : d171209 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171208 p = 1 := by simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17733 p hg
    simpa only [d171209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17735 (p : Pattern) (guard : d171210 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171209 p = 1 := by simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17734 p hg
    simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17736 (p : Pattern) (guard : d171211 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171210 p = 1 := by simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17735 p hg
    simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17737 (p : Pattern) (guard : d171212 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171211 p = 1 := by simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17736 p hg
    simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17738 (p : Pattern) (guard : d171213 p = 1) : d48359 p ≤ (0 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171207 p = 1 := by simpa only [d171213, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17671 p hg
    simpa only [d171213, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171212 p = 1 := by simpa only [d171213, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17737 p hg
    simpa only [d171213, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17739 (p : Pattern) (guard : d2337 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17740 (p : Pattern) (guard : d2338 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2337 p = 1 := by simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17739 p hg
    simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17741 (p : Pattern) (guard : d17378 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17742 (p : Pattern) (guard : d17379 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17378 p = 1 := by simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17741 p hg
    simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17743 (p : Pattern) (guard : d17380 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2338 p = 1 := by simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17740 p hg
    simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17379 p = 1 := by simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17742 p hg
    simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17744 (p : Pattern) (guard : d13815 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17745 (p : Pattern) (guard : d13816 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13815 p = 1 := by simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17744 p hg
    simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17746 (p : Pattern) (guard : d15777 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17747 (p : Pattern) (guard : d15778 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15777 p = 1 := by simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17746 p hg
    simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17748 (p : Pattern) (guard : d17381 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13816 p = 1 := by simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17745 p hg
    simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15778 p = 1 := by simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17747 p hg
    simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17749 (p : Pattern) (guard : d17382 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17380 p = 1 := by simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17743 p hg
    simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17381 p = 1 := by simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17748 p hg
    simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
