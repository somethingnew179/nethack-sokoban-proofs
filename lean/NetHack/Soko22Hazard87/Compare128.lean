import NetHack.Soko22Hazard87.Compare127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32000 (p : Pattern) (guard : d294516 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294515 p = 1 := by simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31999 p hg
    simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32001 (p : Pattern) (guard : d294517 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294516 p = 1 := by simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32000 p hg
    simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32002 (p : Pattern) (guard : d0 p = 1) : d49893 p ≤ (1 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32003 (p : Pattern) (guard : d294518 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294517 p = 1 := by simpa only [d294518, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32001 p hg
    simpa only [d294518, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294518, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294518, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32004 (p : Pattern) (guard : d294519 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294519, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294519, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294518 p = 1 := by simpa only [d294519, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32003 p hg
    simpa only [d294519, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32005 (p : Pattern) (guard : d294520 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294519 p = 1 := by simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32004 p hg
    simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32006 (p : Pattern) (guard : d294521 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294520 p = 1 := by simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32005 p hg
    simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32007 (p : Pattern) (guard : d294522 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294521 p = 1 := by simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32006 p hg
    simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32008 (p : Pattern) (guard : d294523 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294522 p = 1 := by simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32007 p hg
    simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32009 (p : Pattern) (guard : d294524 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294523 p = 1 := by simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32008 p hg
    simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32010 (p : Pattern) (guard : d294525 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294524 p = 1 := by simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32009 p hg
    simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32011 (p : Pattern) (guard : d294526 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294525 p = 1 := by simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32010 p hg
    simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32012 (p : Pattern) (guard : d294527 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294526 p = 1 := by simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32011 p hg
    simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32013 (p : Pattern) (guard : d294528 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294527 p = 1 := by simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32012 p hg
    simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32014 (p : Pattern) (guard : d294529 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294529, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294529, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294528 p = 1 := by simpa only [d294529, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32013 p hg
    simpa only [d294529, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32015 (p : Pattern) (guard : d0 p = 1) : d49885 p ≤ (1 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32016 (p : Pattern) (guard : d0 p = 1) : d49891 p ≤ (1 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32017 (p : Pattern) (guard : d294514 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294514, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d294514, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294513 p = 1 := by simpa only [d294514, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31996 p hg
    simpa only [d294514, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32018 (p : Pattern) (guard : d0 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32019 (p : Pattern) (guard : d294515 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294514 p = 1 := by simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32017 p hg
    simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32020 (p : Pattern) (guard : d294516 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294515 p = 1 := by simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32019 p hg
    simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32021 (p : Pattern) (guard : d294517 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294516 p = 1 := by simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32020 p hg
    simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32022 (p : Pattern) (guard : d294518 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294517 p = 1 := by simpa only [d294518, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32021 p hg
    simpa only [d294518, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294518, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294518, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32023 (p : Pattern) (guard : d294519 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294519, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d294519, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294518 p = 1 := by simpa only [d294519, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32022 p hg
    simpa only [d294519, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32024 (p : Pattern) (guard : d294520 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294519 p = 1 := by simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32023 p hg
    simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32025 (p : Pattern) (guard : d294521 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294520 p = 1 := by simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32024 p hg
    simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32026 (p : Pattern) (guard : d294522 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294521 p = 1 := by simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32025 p hg
    simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32027 (p : Pattern) (guard : d294523 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294522 p = 1 := by simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32026 p hg
    simpa only [d294523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32028 (p : Pattern) (guard : d294524 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294523 p = 1 := by simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32027 p hg
    simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32029 (p : Pattern) (guard : d294525 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294524 p = 1 := by simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32028 p hg
    simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32030 (p : Pattern) (guard : d294526 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294525 p = 1 := by simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32029 p hg
    simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32031 (p : Pattern) (guard : d294527 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294526 p = 1 := by simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32030 p hg
    simpa only [d294527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32032 (p : Pattern) (guard : d294528 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294527 p = 1 := by simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32031 p hg
    simpa only [d294528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32033 (p : Pattern) (guard : d294530 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294522 p = 1 := by simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32007 p hg
    simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32034 (p : Pattern) (guard : d294531 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294530 p = 1 := by simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32033 p hg
    simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32035 (p : Pattern) (guard : d294532 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294531 p = 1 := by simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32034 p hg
    simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32036 (p : Pattern) (guard : d294533 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294532 p = 1 := by simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32035 p hg
    simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32037 (p : Pattern) (guard : d294534 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294533 p = 1 := by simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32036 p hg
    simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32038 (p : Pattern) (guard : d294535 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294534 p = 1 := by simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32037 p hg
    simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32039 (p : Pattern) (guard : d294536 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294528 p = 1 := by simpa only [d294536, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32032 p hg
    simpa only [d294536, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294535 p = 1 := by simpa only [d294536, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32038 p hg
    simpa only [d294536, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32040 (p : Pattern) (guard : d294537 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294529 p = 1 := by simpa only [d294537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32014 p hg
    simpa only [d294537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294536 p = 1 := by simpa only [d294537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32039 p hg
    simpa only [d294537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32041 (p : Pattern) (guard : d294538 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294537 p = 1 := by simpa only [d294538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32040 p hg
    simpa only [d294538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32042 (p : Pattern) (guard : d294539 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294538 p = 1 := by simpa only [d294539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32041 p hg
    simpa only [d294539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32043 (p : Pattern) (guard : d294540 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294539 p = 1 := by simpa only [d294540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32042 p hg
    simpa only [d294540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32044 (p : Pattern) (guard : d0 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32045 (p : Pattern) (guard : d0 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32046 (p : Pattern) (guard : d0 p = 1) : d49990 p ≤ (1 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32047 (p : Pattern) (guard : d0 p = 1) : d49996 p ≤ (1 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32048 (p : Pattern) (guard : d0 p = 1) : d49975 p ≤ (1 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32049 (p : Pattern) (guard : d0 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32050 (p : Pattern) (guard : d0 p = 1) : d49977 p ≤ (1 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32051 (p : Pattern) (guard : d0 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32052 (p : Pattern) (guard : d17 p = 1) : d47706 p ≤ (1 : Int) + d47706 p := by
  omega
theorem compare32053 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32054 (p : Pattern) (guard : d18 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32052 p hg
    simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32053 p hg
    simpa only [d18, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32055 (p : Pattern) (guard : d19 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32054 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32056 (p : Pattern) (guard : d20 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32055 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32057 (p : Pattern) (guard : d29090 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32056 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32058 (p : Pattern) (guard : d294503 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32057 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32059 (p : Pattern) (guard : d0 p = 1) : d49928 p ≤ (1 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32060 (p : Pattern) (guard : d294504 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32058 p hg
    simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d294504, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32061 (p : Pattern) (guard : d0 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32062 (p : Pattern) (guard : d294505 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32060 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32063 (p : Pattern) (guard : d0 p = 1) : d49839 p ≤ (1 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32064 (p : Pattern) (guard : d294506 p = 1) : d49957 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32062 p hg
    simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294506, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32065 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32066 (p : Pattern) (guard : d294507 p = 1) : d49958 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294506 p = 1 := by simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32064 p hg
    simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294507, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32067 (p : Pattern) (guard : d294508 p = 1) : d49978 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294507 p = 1 := by simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32066 p hg
    simpa only [d294508, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32068 (p : Pattern) (guard : d0 p = 1) : d49981 p ≤ (1 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32069 (p : Pattern) (guard : d294509 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294508 p = 1 := by simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32067 p hg
    simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d294509, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32070 (p : Pattern) (guard : d294510 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294509 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32069 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32071 (p : Pattern) (guard : d294511 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294510 p = 1 := by simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32070 p hg
    simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32072 (p : Pattern) (guard : d294512 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294511 p = 1 := by simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32071 p hg
    simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32073 (p : Pattern) (guard : d294513 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294513, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d294513, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294512 p = 1 := by simpa only [d294513, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32072 p hg
    simpa only [d294513, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32074 (p : Pattern) (guard : d294514 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294514, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d294514, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294513 p = 1 := by simpa only [d294514, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32073 p hg
    simpa only [d294514, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32075 (p : Pattern) (guard : d0 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32076 (p : Pattern) (guard : d294515 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294514 p = 1 := by simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32074 p hg
    simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32077 (p : Pattern) (guard : d294516 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294515 p = 1 := by simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32076 p hg
    simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32078 (p : Pattern) (guard : d294517 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294516 p = 1 := by simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32077 p hg
    simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32079 (p : Pattern) (guard : d0 p = 1) : d49998 p ≤ (1 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32080 (p : Pattern) (guard : d294518 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294517 p = 1 := by simpa only [d294518, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32078 p hg
    simpa only [d294518, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294518, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d294518, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32081 (p : Pattern) (guard : d294519 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294519, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d294519, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294518 p = 1 := by simpa only [d294519, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32080 p hg
    simpa only [d294519, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32082 (p : Pattern) (guard : d294520 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294519 p = 1 := by simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32081 p hg
    simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32083 (p : Pattern) (guard : d294521 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294520 p = 1 := by simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32082 p hg
    simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32084 (p : Pattern) (guard : d294522 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294521 p = 1 := by simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32083 p hg
    simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32085 (p : Pattern) (guard : d294530 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294522 p = 1 := by simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32084 p hg
    simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32086 (p : Pattern) (guard : d294531 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294530 p = 1 := by simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32085 p hg
    simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32087 (p : Pattern) (guard : d294532 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294531 p = 1 := by simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32086 p hg
    simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32088 (p : Pattern) (guard : d294533 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294532 p = 1 := by simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32087 p hg
    simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32089 (p : Pattern) (guard : d294534 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294533 p = 1 := by simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32088 p hg
    simpa only [d294534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32090 (p : Pattern) (guard : d294535 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294534 p = 1 := by simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32089 p hg
    simpa only [d294535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32091 (p : Pattern) (guard : d294541 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294541, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294541, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294535 p = 1 := by simpa only [d294541, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32090 p hg
    simpa only [d294541, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32092 (p : Pattern) (guard : d294542 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294541 p = 1 := by simpa only [d294542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32091 p hg
    simpa only [d294542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32093 (p : Pattern) (guard : d294543 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294542 p = 1 := by simpa only [d294543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32092 p hg
    simpa only [d294543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32094 (p : Pattern) (guard : d294544 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294543 p = 1 := by simpa only [d294544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32093 p hg
    simpa only [d294544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32095 (p : Pattern) (guard : d294545 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294544 p = 1 := by simpa only [d294545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32094 p hg
    simpa only [d294545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32096 (p : Pattern) (guard : d294546 p = 1) : d50002 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d294540 p = 1 := by simpa only [d294546, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32043 p hg
    simpa only [d294546, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294545 p = 1 := by simpa only [d294546, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32095 p hg
    simpa only [d294546, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32097 (p : Pattern) (guard : d0 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32098 (p : Pattern) (guard : d0 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32099 (p : Pattern) (guard : d0 p = 1) : d50020 p ≤ (1 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32100 (p : Pattern) (guard : d0 p = 1) : d50029 p ≤ (1 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32101 (p : Pattern) (guard : d0 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32102 (p : Pattern) (guard : d0 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32103 (p : Pattern) (guard : d0 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32104 (p : Pattern) (guard : d17 p = 1) : d47630 p ≤ (1 : Int) + d47630 p := by
  omega
theorem compare32105 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32106 (p : Pattern) (guard : d18 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32104 p hg
    simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32105 p hg
    simpa only [d18, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32107 (p : Pattern) (guard : d19 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32106 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32108 (p : Pattern) (guard : d20 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32107 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32109 (p : Pattern) (guard : d29090 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32108 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32110 (p : Pattern) (guard : d294503 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32109 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32111 (p : Pattern) (guard : d0 p = 1) : d49809 p ≤ (1 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32112 (p : Pattern) (guard : d294504 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32110 p hg
    simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d294504, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32113 (p : Pattern) (guard : d294505 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32112 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32114 (p : Pattern) (guard : d294547 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294505 p = 1 := by simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32113 p hg
    simpa only [d294547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32115 (p : Pattern) (guard : d294506 p = 1) : d50030 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31985 p hg
    simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294506, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32116 (p : Pattern) (guard : d294548 p = 1) : d50031 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294547 p = 1 := by simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32114 p hg
    simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294506 p = 1 := by simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32115 p hg
    simpa only [d294548, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32117 (p : Pattern) (guard : d0 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32118 (p : Pattern) (guard : d17 p = 1) : d47634 p ≤ (1 : Int) + d47634 p := by
  omega
theorem compare32119 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32120 (p : Pattern) (guard : d18 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32118 p hg
    simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32119 p hg
    simpa only [d18, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32121 (p : Pattern) (guard : d19 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32120 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32122 (p : Pattern) (guard : d20 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32121 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32123 (p : Pattern) (guard : d29090 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32122 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32124 (p : Pattern) (guard : d294503 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32123 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32125 (p : Pattern) (guard : d0 p = 1) : d49812 p ≤ (1 : Int) + d47635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32126 (p : Pattern) (guard : d294504 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32124 p hg
    simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d294504, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32127 (p : Pattern) (guard : d0 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32128 (p : Pattern) (guard : d294505 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32126 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32129 (p : Pattern) (guard : d294506 p = 1) : d49865 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32128 p hg
    simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294506, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32130 (p : Pattern) (guard : d294507 p = 1) : d49866 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294506 p = 1 := by simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32129 p hg
    simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294507, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32131 (p : Pattern) (guard : d294549 p = 1) : d50032 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294548 p = 1 := by simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32116 p hg
    simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294507 p = 1 := by simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32130 p hg
    simpa only [d294549, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32132 (p : Pattern) (guard : d0 p = 1) : d50035 p ≤ (1 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32133 (p : Pattern) (guard : d294550 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294549 p = 1 := by simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32131 p hg
    simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d294550, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32134 (p : Pattern) (guard : d294551 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294550 p = 1 := by simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32133 p hg
    simpa only [d294551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32135 (p : Pattern) (guard : d294552 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294551 p = 1 := by simpa only [d294552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32134 p hg
    simpa only [d294552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32136 (p : Pattern) (guard : d294553 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294552 p = 1 := by simpa only [d294553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32135 p hg
    simpa only [d294553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32137 (p : Pattern) (guard : d294554 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294554, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d294554, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294553 p = 1 := by simpa only [d294554, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32136 p hg
    simpa only [d294554, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32138 (p : Pattern) (guard : d294555 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294555, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d294555, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294554 p = 1 := by simpa only [d294555, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32137 p hg
    simpa only [d294555, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32139 (p : Pattern) (guard : d0 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32140 (p : Pattern) (guard : d294556 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294555 p = 1 := by simpa only [d294556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32138 p hg
    simpa only [d294556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32141 (p : Pattern) (guard : d294557 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294556 p = 1 := by simpa only [d294557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32140 p hg
    simpa only [d294557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32142 (p : Pattern) (guard : d294558 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294557 p = 1 := by simpa only [d294558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32141 p hg
    simpa only [d294558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d294558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32143 (p : Pattern) (guard : d0 p = 1) : d50039 p ≤ (1 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32144 (p : Pattern) (guard : d294559 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294558 p = 1 := by simpa only [d294559, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32142 p hg
    simpa only [d294559, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294559, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d294559, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32145 (p : Pattern) (guard : d294560 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294560, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294560, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294559 p = 1 := by simpa only [d294560, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32144 p hg
    simpa only [d294560, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32146 (p : Pattern) (guard : d294561 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294560 p = 1 := by simpa only [d294561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32145 p hg
    simpa only [d294561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32147 (p : Pattern) (guard : d294562 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294561 p = 1 := by simpa only [d294562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32146 p hg
    simpa only [d294562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32148 (p : Pattern) (guard : d294563 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294562 p = 1 := by simpa only [d294563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32147 p hg
    simpa only [d294563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32149 (p : Pattern) (guard : d294564 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294563 p = 1 := by simpa only [d294564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32148 p hg
    simpa only [d294564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32150 (p : Pattern) (guard : d294565 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294564 p = 1 := by simpa only [d294565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32149 p hg
    simpa only [d294565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32151 (p : Pattern) (guard : d294566 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294565 p = 1 := by simpa only [d294566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32150 p hg
    simpa only [d294566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32152 (p : Pattern) (guard : d294567 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294566 p = 1 := by simpa only [d294567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32151 p hg
    simpa only [d294567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32153 (p : Pattern) (guard : d294568 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294567 p = 1 := by simpa only [d294568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32152 p hg
    simpa only [d294568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32154 (p : Pattern) (guard : d294569 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d294569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294568 p = 1 := by simpa only [d294569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32153 p hg
    simpa only [d294569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32155 (p : Pattern) (guard : d294570 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294570, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294570, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294569 p = 1 := by simpa only [d294570, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32154 p hg
    simpa only [d294570, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32156 (p : Pattern) (guard : d294571 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294570 p = 1 := by simpa only [d294571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32155 p hg
    simpa only [d294571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32157 (p : Pattern) (guard : d294572 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294571 p = 1 := by simpa only [d294572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32156 p hg
    simpa only [d294572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32158 (p : Pattern) (guard : d294573 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294572 p = 1 := by simpa only [d294573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32157 p hg
    simpa only [d294573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32159 (p : Pattern) (guard : d294574 p = 1) : d50042 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294573 p = 1 := by simpa only [d294574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32158 p hg
    simpa only [d294574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32097 p hg
    simpa only [d294574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32160 (p : Pattern) (guard : d0 p = 1) : d50099 p ≤ (1 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32161 (p : Pattern) (guard : d294575 p = 1) : d50100 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d294574 p = 1 := by simpa only [d294575, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32159 p hg
    simpa only [d294575, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294575, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32160 p hg
    simpa only [d294575, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32162 (p : Pattern) (guard : d294576 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d294546 p = 1 := by simpa only [d294576, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32096 p hg
    simpa only [d294576, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294575 p = 1 := by simpa only [d294576, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32161 p hg
    simpa only [d294576, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32163 (p : Pattern) (guard : d294577 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294576 p = 1 := by simpa only [d294577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32162 p hg
    simpa only [d294577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32164 (p : Pattern) (guard : d294578 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294577 p = 1 := by simpa only [d294578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32163 p hg
    simpa only [d294578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32165 (p : Pattern) (guard : d294579 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294578 p = 1 := by simpa only [d294579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32164 p hg
    simpa only [d294579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32166 (p : Pattern) (guard : d294580 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294579 p = 1 := by simpa only [d294580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32165 p hg
    simpa only [d294580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32167 (p : Pattern) (guard : d294581 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294580 p = 1 := by simpa only [d294581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32166 p hg
    simpa only [d294581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32168 (p : Pattern) (guard : d294582 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294581 p = 1 := by simpa only [d294582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32167 p hg
    simpa only [d294582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32169 (p : Pattern) (guard : d294583 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d294583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294582 p = 1 := by simpa only [d294583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32168 p hg
    simpa only [d294583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32170 (p : Pattern) (guard : d205892 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31980 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32171 (p : Pattern) (guard : d205893 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32170 p hg
    simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d205893, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32172 (p : Pattern) (guard : d205894 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32171 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32173 (p : Pattern) (guard : d205895 p = 1) : d49838 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32172 p hg
    simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d205895, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32174 (p : Pattern) (guard : d205896 p = 1) : d49841 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205895 p = 1 := by simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32173 p hg
    simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d205896, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32175 (p : Pattern) (guard : d205897 p = 1) : d49864 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205896 p = 1 := by simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32174 p hg
    simpa only [d205897, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32176 (p : Pattern) (guard : d205898 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d205897 p = 1 := by simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32175 p hg
    simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d205898, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32177 (p : Pattern) (guard : d294584 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205898 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32176 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32178 (p : Pattern) (guard : d294585 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294510 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31993 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294584 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32177 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32179 (p : Pattern) (guard : d205899 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d205898 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32176 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32180 (p : Pattern) (guard : d294586 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294584 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32177 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205899 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32179 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32181 (p : Pattern) (guard : d294587 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294585 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32178 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294586 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32180 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32182 (p : Pattern) (guard : d294588 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294587 p = 1 := by simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32181 p hg
    simpa only [d294588, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32183 (p : Pattern) (guard : d294589 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294588 p = 1 := by simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32182 p hg
    simpa only [d294589, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32184 (p : Pattern) (guard : d205900 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d205899 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32179 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32185 (p : Pattern) (guard : d294590 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294586 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32180 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205900 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32184 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32186 (p : Pattern) (guard : d294591 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294590 p = 1 := by simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32185 p hg
    simpa only [d294591, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32187 (p : Pattern) (guard : d294592 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294591 p = 1 := by simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32186 p hg
    simpa only [d294592, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32188 (p : Pattern) (guard : d294593 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294589 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32183 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294592 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32187 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32189 (p : Pattern) (guard : d294594 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294592 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32187 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32190 (p : Pattern) (guard : d294595 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294593 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32188 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294594 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32189 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32191 (p : Pattern) (guard : d294596 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294595 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32190 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32192 (p : Pattern) (guard : d294597 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294596 p = 1 := by simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32191 p hg
    simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294597, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32193 (p : Pattern) (guard : d294598 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294597 p = 1 := by simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d294598, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32194 (p : Pattern) (guard : d294599 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294594 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32189 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32195 (p : Pattern) (guard : d294600 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294599 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32194 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32196 (p : Pattern) (guard : d294601 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294600 p = 1 := by simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32195 p hg
    simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294601, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32197 (p : Pattern) (guard : d294602 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294601 p = 1 := by simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32196 p hg
    simpa only [d294602, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32198 (p : Pattern) (guard : d294603 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294602 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32197 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32199 (p : Pattern) (guard : d294604 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294603 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32198 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32200 (p : Pattern) (guard : d294605 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294604 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32199 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32201 (p : Pattern) (guard : d294606 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294605 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32200 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32202 (p : Pattern) (guard : d294607 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294602 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32197 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32203 (p : Pattern) (guard : d294608 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294607 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32202 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32204 (p : Pattern) (guard : d294609 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294608 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32203 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32205 (p : Pattern) (guard : d294610 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294609 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32204 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32206 (p : Pattern) (guard : d294611 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294606 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32201 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294610 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32205 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32207 (p : Pattern) (guard : d294612 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294611 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32206 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32208 (p : Pattern) (guard : d294613 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294612 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32207 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32209 (p : Pattern) (guard : d294614 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294613 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32208 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32210 (p : Pattern) (guard : d294615 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294614 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32209 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32211 (p : Pattern) (guard : d294616 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294615 p = 1 := by simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32210 p hg
    simpa only [d294616, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32212 (p : Pattern) (guard : d294617 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294616 p = 1 := by simpa only [d294617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32211 p hg
    simpa only [d294617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32213 (p : Pattern) (guard : d294618 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294617 p = 1 := by simpa only [d294618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32212 p hg
    simpa only [d294618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32214 (p : Pattern) (guard : d294589 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294588 p = 1 := by simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32182 p hg
    simpa only [d294589, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32215 (p : Pattern) (guard : d294592 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294591 p = 1 := by simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32186 p hg
    simpa only [d294592, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32216 (p : Pattern) (guard : d294593 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294589 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32214 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294592 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32215 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32217 (p : Pattern) (guard : d294594 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294592 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32215 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32218 (p : Pattern) (guard : d294595 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294593 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32216 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294594 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32217 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32219 (p : Pattern) (guard : d294596 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294595 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32218 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32220 (p : Pattern) (guard : d294597 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294596 p = 1 := by simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32219 p hg
    simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294597, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32221 (p : Pattern) (guard : d294598 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294597 p = 1 := by simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32220 p hg
    simpa only [d294598, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32222 (p : Pattern) (guard : d294599 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294594 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32217 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32223 (p : Pattern) (guard : d294600 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294599 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32222 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32224 (p : Pattern) (guard : d294601 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294600 p = 1 := by simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32223 p hg
    simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294601, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32225 (p : Pattern) (guard : d294602 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294601 p = 1 := by simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32224 p hg
    simpa only [d294602, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32226 (p : Pattern) (guard : d294603 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32221 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294602 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32225 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32227 (p : Pattern) (guard : d294604 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294603 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32226 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32228 (p : Pattern) (guard : d294605 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294604 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32227 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32229 (p : Pattern) (guard : d294606 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294605 p = 1 := by simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32228 p hg
    simpa only [d294606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32230 (p : Pattern) (guard : d294607 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294602 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32225 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32231 (p : Pattern) (guard : d294608 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294607 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32230 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32232 (p : Pattern) (guard : d294609 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294608 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32231 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32233 (p : Pattern) (guard : d294610 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294609 p = 1 := by simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32232 p hg
    simpa only [d294610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32234 (p : Pattern) (guard : d294611 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294606 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32229 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294610 p = 1 := by simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32233 p hg
    simpa only [d294611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32235 (p : Pattern) (guard : d294612 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294611 p = 1 := by simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32234 p hg
    simpa only [d294612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32236 (p : Pattern) (guard : d294613 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294612 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32235 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32237 (p : Pattern) (guard : d294614 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294613 p = 1 := by simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32236 p hg
    simpa only [d294614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32238 (p : Pattern) (guard : d294615 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294614 p = 1 := by simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32237 p hg
    simpa only [d294615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32239 (p : Pattern) (guard : d294619 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294605 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32200 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32240 (p : Pattern) (guard : d294620 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294609 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32204 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32241 (p : Pattern) (guard : d294621 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294619 p = 1 := by simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32239 p hg
    simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294620 p = 1 := by simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32240 p hg
    simpa only [d294621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32242 (p : Pattern) (guard : d294622 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294621 p = 1 := by simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32241 p hg
    simpa only [d294622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32243 (p : Pattern) (guard : d294623 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294622 p = 1 := by simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32242 p hg
    simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32244 (p : Pattern) (guard : d294624 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294623 p = 1 := by simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32243 p hg
    simpa only [d294624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32245 (p : Pattern) (guard : d294625 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294624 p = 1 := by simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32244 p hg
    simpa only [d294625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32246 (p : Pattern) (guard : d294626 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294615 p = 1 := by simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32238 p hg
    simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294625 p = 1 := by simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32245 p hg
    simpa only [d294626, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32247 (p : Pattern) (guard : d294627 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294616 p = 1 := by simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32211 p hg
    simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294626 p = 1 := by simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32246 p hg
    simpa only [d294627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32248 (p : Pattern) (guard : d294628 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294627 p = 1 := by simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32247 p hg
    simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32249 (p : Pattern) (guard : d294629 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294618 p = 1 := by simpa only [d294629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32213 p hg
    simpa only [d294629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294628 p = 1 := by simpa only [d294629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32248 p hg
    simpa only [d294629, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
