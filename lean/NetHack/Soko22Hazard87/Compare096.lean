import NetHack.Soko22Hazard87.Compare095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24000 (p : Pattern) (guard : d180140 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180139 p = 1 := by simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23999 p hg
    simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24001 (p : Pattern) (guard : d180150 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare24002 (p : Pattern) (guard : d180151 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180150 p = 1 := by simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24001 p hg
    simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24003 (p : Pattern) (guard : d180152 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180151 p = 1 := by simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24002 p hg
    simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24004 (p : Pattern) (guard : d180153 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180152 p = 1 := by simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24003 p hg
    simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24005 (p : Pattern) (guard : d180154 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180140 p = 1 := by simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24000 p hg
    simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180153 p = 1 := by simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24004 p hg
    simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24006 (p : Pattern) (guard : d180155 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180154 p = 1 := by simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24005 p hg
    simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24007 (p : Pattern) (guard : d180156 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180155 p = 1 := by simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24006 p hg
    simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24008 (p : Pattern) (guard : d180157 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180153 p = 1 := by simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24004 p hg
    simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24009 (p : Pattern) (guard : d180158 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180157 p = 1 := by simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24008 p hg
    simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24010 (p : Pattern) (guard : d180159 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180158 p = 1 := by simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24009 p hg
    simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24011 (p : Pattern) (guard : d180160 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180156 p = 1 := by simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24007 p hg
    simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180159 p = 1 := by simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24010 p hg
    simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24012 (p : Pattern) (guard : d180165 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180159 p = 1 := by simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24010 p hg
    simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24013 (p : Pattern) (guard : d180166 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180160 p = 1 := by simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24011 p hg
    simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180165 p = 1 := by simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24012 p hg
    simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24014 (p : Pattern) (guard : d180167 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180166 p = 1 := by simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24013 p hg
    simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24015 (p : Pattern) (guard : d180168 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180167 p = 1 := by simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24014 p hg
    simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24016 (p : Pattern) (guard : d180169 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180168 p = 1 := by simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24015 p hg
    simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24017 (p : Pattern) (guard : d180174 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180165 p = 1 := by simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24012 p hg
    simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24018 (p : Pattern) (guard : d180175 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180174 p = 1 := by simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24017 p hg
    simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24019 (p : Pattern) (guard : d180176 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180175 p = 1 := by simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24018 p hg
    simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24020 (p : Pattern) (guard : d180177 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180176 p = 1 := by simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24019 p hg
    simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24021 (p : Pattern) (guard : d180178 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180169 p = 1 := by simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24016 p hg
    simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180177 p = 1 := by simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24020 p hg
    simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24022 (p : Pattern) (guard : d180179 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180178 p = 1 := by simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24021 p hg
    simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24023 (p : Pattern) (guard : d180180 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180179 p = 1 := by simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24022 p hg
    simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24024 (p : Pattern) (guard : d180181 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180180 p = 1 := by simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24023 p hg
    simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24025 (p : Pattern) (guard : d180195 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180177 p = 1 := by simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24020 p hg
    simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24026 (p : Pattern) (guard : d180196 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180195 p = 1 := by simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24025 p hg
    simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24027 (p : Pattern) (guard : d180197 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180196 p = 1 := by simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24026 p hg
    simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24028 (p : Pattern) (guard : d180198 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180197 p = 1 := by simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24027 p hg
    simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24029 (p : Pattern) (guard : d180546 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180181 p = 1 := by simpa only [d180546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24024 p hg
    simpa only [d180546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180198 p = 1 := by simpa only [d180546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24028 p hg
    simpa only [d180546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24030 (p : Pattern) (guard : d180547 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180546 p = 1 := by simpa only [d180547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24029 p hg
    simpa only [d180547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24031 (p : Pattern) (guard : d180548 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180547 p = 1 := by simpa only [d180548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24030 p hg
    simpa only [d180548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24032 (p : Pattern) (guard : d180549 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180548 p = 1 := by simpa only [d180549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24031 p hg
    simpa only [d180549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24033 (p : Pattern) (guard : d180550 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180549 p = 1 := by simpa only [d180550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24032 p hg
    simpa only [d180550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24034 (p : Pattern) (guard : d180551 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180551, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180551, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180550 p = 1 := by simpa only [d180551, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24033 p hg
    simpa only [d180551, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24035 (p : Pattern) (guard : d180552 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180551 p = 1 := by simpa only [d180552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24034 p hg
    simpa only [d180552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24036 (p : Pattern) (guard : d180553 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180552 p = 1 := by simpa only [d180553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24035 p hg
    simpa only [d180553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24037 (p : Pattern) (guard : d180554 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180553 p = 1 := by simpa only [d180554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24036 p hg
    simpa only [d180554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24038 (p : Pattern) (guard : d180555 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180554 p = 1 := by simpa only [d180555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24037 p hg
    simpa only [d180555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24039 (p : Pattern) (guard : d180556 p = 1) : d48387 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180555 p = 1 := by simpa only [d180556, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24038 p hg
    simpa only [d180556, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180556, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23415 p hg
    simpa only [d180556, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24040 (p : Pattern) (guard : d180557 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d180545 p = 1 := by simpa only [d180557, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23996 p hg
    simpa only [d180557, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180556 p = 1 := by simpa only [d180557, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24039 p hg
    simpa only [d180557, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24041 (p : Pattern) (guard : d180558 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180557 p = 1 := by simpa only [d180558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24040 p hg
    simpa only [d180558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24042 (p : Pattern) (guard : d180559 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180558 p = 1 := by simpa only [d180559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24041 p hg
    simpa only [d180559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24043 (p : Pattern) (guard : d180560 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180559 p = 1 := by simpa only [d180560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24042 p hg
    simpa only [d180560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24044 (p : Pattern) (guard : d180561 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180560 p = 1 := by simpa only [d180561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24043 p hg
    simpa only [d180561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24045 (p : Pattern) (guard : d180562 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180561 p = 1 := by simpa only [d180562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24044 p hg
    simpa only [d180562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24046 (p : Pattern) (guard : d180563 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180562 p = 1 := by simpa only [d180563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24045 p hg
    simpa only [d180563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24047 (p : Pattern) (guard : d180564 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180563 p = 1 := by simpa only [d180564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24046 p hg
    simpa only [d180564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24048 (p : Pattern) (guard : d180565 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180564 p = 1 := by simpa only [d180565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24047 p hg
    simpa only [d180565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24049 (p : Pattern) (guard : d180566 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180565 p = 1 := by simpa only [d180566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24048 p hg
    simpa only [d180566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24050 (p : Pattern) (guard : d180567 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180566 p = 1 := by simpa only [d180567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24049 p hg
    simpa only [d180567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24051 (p : Pattern) (guard : d180568 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d180537 p = 1 := by simpa only [d180568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23878 p hg
    simpa only [d180568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180567 p = 1 := by simpa only [d180568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24050 p hg
    simpa only [d180568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24052 (p : Pattern) (guard : d180569 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d180568 p = 1 := by simpa only [d180569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24051 p hg
    simpa only [d180569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24053 (p : Pattern) (guard : d180570 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d180569 p = 1 := by simpa only [d180570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24052 p hg
    simpa only [d180570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24054 (p : Pattern) (guard : d180571 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d180570 p = 1 := by simpa only [d180571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24053 p hg
    simpa only [d180571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24055 (p : Pattern) (guard : d180572 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d180571 p = 1 := by simpa only [d180572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24054 p hg
    simpa only [d180572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24056 (p : Pattern) (guard : d180573 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d180572 p = 1 := by simpa only [d180573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24055 p hg
    simpa only [d180573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24057 (p : Pattern) (guard : d180574 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d180573 p = 1 := by simpa only [d180574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24056 p hg
    simpa only [d180574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24058 (p : Pattern) (guard : d180575 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d180574 p = 1 := by simpa only [d180575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24057 p hg
    simpa only [d180575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24059 (p : Pattern) (guard : d180576 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d180575 p = 1 := by simpa only [d180576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24058 p hg
    simpa only [d180576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24060 (p : Pattern) (guard : d180577 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d180576 p = 1 := by simpa only [d180577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24059 p hg
    simpa only [d180577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24061 (p : Pattern) (guard : d180578 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d180577 p = 1 := by simpa only [d180578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24060 p hg
    simpa only [d180578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24062 (p : Pattern) (guard : d180579 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d180578 p = 1 := by simpa only [d180579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24061 p hg
    simpa only [d180579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24063 (p : Pattern) (guard : d180580 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d180579 p = 1 := by simpa only [d180580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24062 p hg
    simpa only [d180580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24064 (p : Pattern) (guard : d180581 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d180580 p = 1 := by simpa only [d180581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24063 p hg
    simpa only [d180581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24065 (p : Pattern) (guard : d180582 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d180581 p = 1 := by simpa only [d180582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24064 p hg
    simpa only [d180582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24066 (p : Pattern) (guard : d180583 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d180582 p = 1 := by simpa only [d180583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24065 p hg
    simpa only [d180583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24067 (p : Pattern) (guard : d180584 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d180583 p = 1 := by simpa only [d180584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24066 p hg
    simpa only [d180584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24068 (p : Pattern) (guard : d180585 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d180584 p = 1 := by simpa only [d180585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24067 p hg
    simpa only [d180585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24069 (p : Pattern) (guard : d180586 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d180585 p = 1 := by simpa only [d180586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24068 p hg
    simpa only [d180586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24070 (p : Pattern) (guard : d180587 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d180586 p = 1 := by simpa only [d180587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24069 p hg
    simpa only [d180587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24071 (p : Pattern) (guard : d180588 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d180587 p = 1 := by simpa only [d180588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24070 p hg
    simpa only [d180588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24072 (p : Pattern) (guard : d180589 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d180588 p = 1 := by simpa only [d180589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24071 p hg
    simpa only [d180589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24073 (p : Pattern) (guard : d180590 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d180589 p = 1 := by simpa only [d180590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24072 p hg
    simpa only [d180590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24074 (p : Pattern) (guard : d180591 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d180590 p = 1 := by simpa only [d180591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24073 p hg
    simpa only [d180591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24075 (p : Pattern) (guard : d180592 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d180591 p = 1 := by simpa only [d180592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24074 p hg
    simpa only [d180592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24076 (p : Pattern) (guard : d180593 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d180592 p = 1 := by simpa only [d180593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24075 p hg
    simpa only [d180593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24077 (p : Pattern) (guard : d180594 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d180593 p = 1 := by simpa only [d180594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24076 p hg
    simpa only [d180594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24078 (p : Pattern) (guard : d180595 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d180594 p = 1 := by simpa only [d180595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24077 p hg
    simpa only [d180595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24079 (p : Pattern) (guard : d180596 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d180595 p = 1 := by simpa only [d180596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24078 p hg
    simpa only [d180596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24080 (p : Pattern) (guard : d180597 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d180596 p = 1 := by simpa only [d180597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24079 p hg
    simpa only [d180597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24081 (p : Pattern) (guard : d180598 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d180597 p = 1 := by simpa only [d180598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24080 p hg
    simpa only [d180598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24082 (p : Pattern) (guard : d180599 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d180598 p = 1 := by simpa only [d180599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24081 p hg
    simpa only [d180599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24083 (p : Pattern) (guard : d180600 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d180599 p = 1 := by simpa only [d180600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24082 p hg
    simpa only [d180600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24084 (p : Pattern) (guard : d180601 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d180600 p = 1 := by simpa only [d180601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d180601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24085 (p : Pattern) (guard : d180602 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d180601 p = 1 := by simpa only [d180602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24084 p hg
    simpa only [d180602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24086 (p : Pattern) (guard : d180603 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d180602 p = 1 := by simpa only [d180603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24085 p hg
    simpa only [d180603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24087 (p : Pattern) (guard : d180604 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d180603 p = 1 := by simpa only [d180604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24086 p hg
    simpa only [d180604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24088 (p : Pattern) (guard : d180605 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d180604 p = 1 := by simpa only [d180605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24087 p hg
    simpa only [d180605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24089 (p : Pattern) (guard : d180606 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d180605 p = 1 := by simpa only [d180606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24088 p hg
    simpa only [d180606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24090 (p : Pattern) (guard : d180607 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d180606 p = 1 := by simpa only [d180607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24089 p hg
    simpa only [d180607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24091 (p : Pattern) (guard : d180608 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d180607 p = 1 := by simpa only [d180608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24090 p hg
    simpa only [d180608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24092 (p : Pattern) (guard : d180609 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d180608 p = 1 := by simpa only [d180609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24091 p hg
    simpa only [d180609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24093 (p : Pattern) (guard : d180610 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d180609 p = 1 := by simpa only [d180610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24092 p hg
    simpa only [d180610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24094 (p : Pattern) (guard : d180611 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d180610 p = 1 := by simpa only [d180611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24093 p hg
    simpa only [d180611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24095 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-1 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24096 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-2 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24097 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (1 : Int) + d181866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24098 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (0 : Int) + d181866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24099 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-1 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24100 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-2 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24101 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (1 : Int) + d184679 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24102 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (0 : Int) + d184679 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24103 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-1 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24104 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-2 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24105 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-1 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24106 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-2 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24107 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-1 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24108 (p : Pattern) (guard : d0 p = 1) : d48547 p ≤ (-2 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24109 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-1 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24110 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-2 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24111 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-1 : Int) + d48997 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24112 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-2 : Int) + d48997 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24113 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24114 (p : Pattern) (guard : d0 p = 1) : d48697 p ≤ (3 : Int) + d130446 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24115 (p : Pattern) (guard : d0 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24116 (p : Pattern) (guard : d0 p = 1) : d48613 p ≤ (3 : Int) + d130418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24117 (p : Pattern) (guard : d0 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24118 (p : Pattern) (guard : d0 p = 1) : d48630 p ≤ (3 : Int) + d130415 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24119 (p : Pattern) (guard : d0 p = 1) : d48635 p ≤ (3 : Int) + d130404 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24120 (p : Pattern) (guard : d0 p = 1) : d48602 p ≤ (3 : Int) + d130406 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24121 (p : Pattern) (guard : d66 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24122 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (3 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24123 (p : Pattern) (guard : d18534 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d66 p = 1 := by simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24121 p hg
    simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18534, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24124 (p : Pattern) (guard : d0 p = 1) : d48571 p ≤ (3 : Int) + d130398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24125 (p : Pattern) (guard : d180909 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18534 p = 1 := by simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24123 p hg
    simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d180909, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24126 (p : Pattern) (guard : d0 p = 1) : d48700 p ≤ (3 : Int) + d48700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24127 (p : Pattern) (guard : d180910 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180909 p = 1 := by simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24125 p hg
    simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d180910, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24128 (p : Pattern) (guard : d0 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24129 (p : Pattern) (guard : d180911 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180910 p = 1 := by simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24127 p hg
    simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d180911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24130 (p : Pattern) (guard : d180912 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180911 p = 1 := by simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24129 p hg
    simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d180912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24131 (p : Pattern) (guard : d180913 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180912 p = 1 := by simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24130 p hg
    simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d180913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24132 (p : Pattern) (guard : d180914 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180913 p = 1 := by simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24131 p hg
    simpa only [d180914, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24133 (p : Pattern) (guard : d180915 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180914 p = 1 := by simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24132 p hg
    simpa only [d180915, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24134 (p : Pattern) (guard : d0 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24135 (p : Pattern) (guard : d180916 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180915 p = 1 := by simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24133 p hg
    simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d180916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24136 (p : Pattern) (guard : d180917 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180916 p = 1 := by simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24135 p hg
    simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d180917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24137 (p : Pattern) (guard : d180918 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180917 p = 1 := by simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24136 p hg
    simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d180918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24138 (p : Pattern) (guard : d0 p = 1) : d48704 p ≤ (3 : Int) + d130451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24139 (p : Pattern) (guard : d180919 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180918 p = 1 := by simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24137 p hg
    simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d180919, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24140 (p : Pattern) (guard : d180920 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180919 p = 1 := by simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24139 p hg
    simpa only [d180920, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24141 (p : Pattern) (guard : d180921 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180920 p = 1 := by simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24140 p hg
    simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24142 (p : Pattern) (guard : d180922 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180921 p = 1 := by simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24141 p hg
    simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24143 (p : Pattern) (guard : d180923 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180922 p = 1 := by simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24142 p hg
    simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24144 (p : Pattern) (guard : d180924 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180923 p = 1 := by simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24143 p hg
    simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24145 (p : Pattern) (guard : d180925 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180924 p = 1 := by simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24144 p hg
    simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24146 (p : Pattern) (guard : d180926 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180925 p = 1 := by simpa only [d180926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24145 p hg
    simpa only [d180926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24147 (p : Pattern) (guard : d180927 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180926 p = 1 := by simpa only [d180927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24146 p hg
    simpa only [d180927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24148 (p : Pattern) (guard : d180928 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180927 p = 1 := by simpa only [d180928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24147 p hg
    simpa only [d180928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24149 (p : Pattern) (guard : d180929 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180928 p = 1 := by simpa only [d180929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24148 p hg
    simpa only [d180929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24150 (p : Pattern) (guard : d180930 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180930, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d180930, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180929 p = 1 := by simpa only [d180930, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24149 p hg
    simpa only [d180930, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24151 (p : Pattern) (guard : d180931 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180930 p = 1 := by simpa only [d180931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24150 p hg
    simpa only [d180931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24152 (p : Pattern) (guard : d180932 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180931 p = 1 := by simpa only [d180932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24151 p hg
    simpa only [d180932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24153 (p : Pattern) (guard : d180933 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180932 p = 1 := by simpa only [d180933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24152 p hg
    simpa only [d180933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24154 (p : Pattern) (guard : d180934 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180933 p = 1 := by simpa only [d180934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24153 p hg
    simpa only [d180934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24155 (p : Pattern) (guard : d0 p = 1) : d48747 p ≤ (3 : Int) + d130477 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24156 (p : Pattern) (guard : d180935 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180934 p = 1 := by simpa only [d180935, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24154 p hg
    simpa only [d180935, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180935, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d180935, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24157 (p : Pattern) (guard : d180936 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180936, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d180936, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180935 p = 1 := by simpa only [d180936, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24156 p hg
    simpa only [d180936, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24158 (p : Pattern) (guard : d180937 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180936 p = 1 := by simpa only [d180937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24157 p hg
    simpa only [d180937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24159 (p : Pattern) (guard : d180938 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180937 p = 1 := by simpa only [d180938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24158 p hg
    simpa only [d180938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24160 (p : Pattern) (guard : d180939 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180938 p = 1 := by simpa only [d180939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24159 p hg
    simpa only [d180939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24161 (p : Pattern) (guard : d180940 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180939 p = 1 := by simpa only [d180940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24160 p hg
    simpa only [d180940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24162 (p : Pattern) (guard : d226 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24163 (p : Pattern) (guard : d18571 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d226 p = 1 := by simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24162 p hg
    simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18571, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24164 (p : Pattern) (guard : d180941 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18571 p = 1 := by simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24163 p hg
    simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d180941, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24165 (p : Pattern) (guard : d180942 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180941 p = 1 := by simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24164 p hg
    simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d180942, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24166 (p : Pattern) (guard : d180943 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180942 p = 1 := by simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24165 p hg
    simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180910 p = 1 := by simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24127 p hg
    simpa only [d180943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24167 (p : Pattern) (guard : d180944 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180943 p = 1 := by simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24166 p hg
    simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180911 p = 1 := by simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24129 p hg
    simpa only [d180944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24168 (p : Pattern) (guard : d180945 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180944 p = 1 := by simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24167 p hg
    simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180912 p = 1 := by simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24130 p hg
    simpa only [d180945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24169 (p : Pattern) (guard : d180946 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180945 p = 1 := by simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24168 p hg
    simpa only [d180946, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24170 (p : Pattern) (guard : d180947 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180946 p = 1 := by simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24169 p hg
    simpa only [d180947, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24171 (p : Pattern) (guard : d180948 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180947 p = 1 := by simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24170 p hg
    simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180915 p = 1 := by simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24133 p hg
    simpa only [d180948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24172 (p : Pattern) (guard : d180949 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180948 p = 1 := by simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24171 p hg
    simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180916 p = 1 := by simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24135 p hg
    simpa only [d180949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24173 (p : Pattern) (guard : d180950 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180949 p = 1 := by simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24172 p hg
    simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d180950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24174 (p : Pattern) (guard : d180951 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180950 p = 1 := by simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24173 p hg
    simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d180951, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24175 (p : Pattern) (guard : d180952 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180951 p = 1 := by simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24174 p hg
    simpa only [d180952, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24176 (p : Pattern) (guard : d180953 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180952 p = 1 := by simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24175 p hg
    simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180920 p = 1 := by simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24140 p hg
    simpa only [d180953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24177 (p : Pattern) (guard : d180954 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180953 p = 1 := by simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24176 p hg
    simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24178 (p : Pattern) (guard : d180955 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180954 p = 1 := by simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24177 p hg
    simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24179 (p : Pattern) (guard : d180956 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180955 p = 1 := by simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24178 p hg
    simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24180 (p : Pattern) (guard : d180957 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180956 p = 1 := by simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24179 p hg
    simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180924 p = 1 := by simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24144 p hg
    simpa only [d180957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24181 (p : Pattern) (guard : d180958 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180957 p = 1 := by simpa only [d180958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24180 p hg
    simpa only [d180958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24182 (p : Pattern) (guard : d180959 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180958 p = 1 := by simpa only [d180959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24181 p hg
    simpa only [d180959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180926 p = 1 := by simpa only [d180959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24146 p hg
    simpa only [d180959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24183 (p : Pattern) (guard : d180960 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180959 p = 1 := by simpa only [d180960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24182 p hg
    simpa only [d180960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24184 (p : Pattern) (guard : d180961 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180960 p = 1 := by simpa only [d180961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24183 p hg
    simpa only [d180961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24185 (p : Pattern) (guard : d180962 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180962, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d180962, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180961 p = 1 := by simpa only [d180962, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24184 p hg
    simpa only [d180962, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24186 (p : Pattern) (guard : d180963 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180962 p = 1 := by simpa only [d180963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24185 p hg
    simpa only [d180963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24187 (p : Pattern) (guard : d180964 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180963 p = 1 := by simpa only [d180964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24186 p hg
    simpa only [d180964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24188 (p : Pattern) (guard : d180965 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180964 p = 1 := by simpa only [d180965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24187 p hg
    simpa only [d180965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24189 (p : Pattern) (guard : d180966 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180965 p = 1 := by simpa only [d180966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24188 p hg
    simpa only [d180966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d180966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24190 (p : Pattern) (guard : d180967 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180966 p = 1 := by simpa only [d180967, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24189 p hg
    simpa only [d180967, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180967, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d180967, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24191 (p : Pattern) (guard : d180968 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180968, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d180968, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180967 p = 1 := by simpa only [d180968, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24190 p hg
    simpa only [d180968, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24192 (p : Pattern) (guard : d180969 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180968 p = 1 := by simpa only [d180969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24191 p hg
    simpa only [d180969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24193 (p : Pattern) (guard : d180970 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180969 p = 1 := by simpa only [d180970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24192 p hg
    simpa only [d180970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24194 (p : Pattern) (guard : d180971 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180970 p = 1 := by simpa only [d180971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24193 p hg
    simpa only [d180971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24195 (p : Pattern) (guard : d180972 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d180972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180971 p = 1 := by simpa only [d180972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24194 p hg
    simpa only [d180972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24196 (p : Pattern) (guard : d180973 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d180940 p = 1 := by simpa only [d180973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24161 p hg
    simpa only [d180973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180972 p = 1 := by simpa only [d180973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24195 p hg
    simpa only [d180973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24197 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24198 (p : Pattern) (guard : d18631 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24197 p hg
    simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24199 (p : Pattern) (guard : d180974 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18631 p = 1 := by simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24198 p hg
    simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24200 (p : Pattern) (guard : d180975 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180974 p = 1 := by simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24199 p hg
    simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24201 (p : Pattern) (guard : d180976 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180975 p = 1 := by simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24200 p hg
    simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180942 p = 1 := by simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24165 p hg
    simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24202 (p : Pattern) (guard : d12599 p = 1) : d47652 p ≤ (3 : Int) + d47652 p := by
  omega
theorem compare24203 (p : Pattern) (guard : d18635 p = 1) : d48567 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d12599 p = 1 := by simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24202 p hg
    simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24204 (p : Pattern) (guard : d180977 p = 1) : d48698 p ≤ (3 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18635 p = 1 := by simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24203 p hg
    simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24205 (p : Pattern) (guard : d180978 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180977 p = 1 := by simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24204 p hg
    simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24206 (p : Pattern) (guard : d180979 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180978 p = 1 := by simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24205 p hg
    simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180910 p = 1 := by simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24127 p hg
    simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24207 (p : Pattern) (guard : d180980 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180976 p = 1 := by simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24201 p hg
    simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180979 p = 1 := by simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24206 p hg
    simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24208 (p : Pattern) (guard : d180981 p = 1) : d48701 p ≤ (3 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180980 p = 1 := by simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24207 p hg
    simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180944 p = 1 := by simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24167 p hg
    simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24209 (p : Pattern) (guard : d180982 p = 1) : d48702 p ≤ (3 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180981 p = 1 := by simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24208 p hg
    simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24210 (p : Pattern) (guard : d180983 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180982 p = 1 := by simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24209 p hg
    simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24211 (p : Pattern) (guard : d180984 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180983 p = 1 := by simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24210 p hg
    simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180947 p = 1 := by simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24170 p hg
    simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24212 (p : Pattern) (guard : d180985 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180984 p = 1 := by simpa only [d180985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24211 p hg
    simpa only [d180985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180948 p = 1 := by simpa only [d180985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24171 p hg
    simpa only [d180985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24213 (p : Pattern) (guard : d180986 p = 1) : d48703 p ≤ (3 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180985 p = 1 := by simpa only [d180986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24212 p hg
    simpa only [d180986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d180986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24214 (p : Pattern) (guard : d180987 p = 1) : d48705 p ≤ (3 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180986 p = 1 := by simpa only [d180987, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24213 p hg
    simpa only [d180987, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180987, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d180987, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24215 (p : Pattern) (guard : d180988 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180988, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d180988, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180987 p = 1 := by simpa only [d180988, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24214 p hg
    simpa only [d180988, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24216 (p : Pattern) (guard : d180989 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180988 p = 1 := by simpa only [d180989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24215 p hg
    simpa only [d180989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180952 p = 1 := by simpa only [d180989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24175 p hg
    simpa only [d180989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24217 (p : Pattern) (guard : d180990 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180989 p = 1 := by simpa only [d180990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24216 p hg
    simpa only [d180990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24218 (p : Pattern) (guard : d180991 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180990 p = 1 := by simpa only [d180991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24217 p hg
    simpa only [d180991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24219 (p : Pattern) (guard : d180992 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180991 p = 1 := by simpa only [d180992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24218 p hg
    simpa only [d180992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24220 (p : Pattern) (guard : d180993 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180992 p = 1 := by simpa only [d180993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24219 p hg
    simpa only [d180993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180956 p = 1 := by simpa only [d180993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24179 p hg
    simpa only [d180993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24221 (p : Pattern) (guard : d180994 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180993 p = 1 := by simpa only [d180994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24220 p hg
    simpa only [d180994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24222 (p : Pattern) (guard : d180995 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180952 p = 1 := by simpa only [d180995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24175 p hg
    simpa only [d180995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24223 (p : Pattern) (guard : d180996 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180995 p = 1 := by simpa only [d180996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24222 p hg
    simpa only [d180996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24224 (p : Pattern) (guard : d180997 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180996 p = 1 := by simpa only [d180997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24223 p hg
    simpa only [d180997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24225 (p : Pattern) (guard : d180998 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180997 p = 1 := by simpa only [d180998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24224 p hg
    simpa only [d180998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24226 (p : Pattern) (guard : d180999 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180998 p = 1 := by simpa only [d180999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24225 p hg
    simpa only [d180999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d180999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24227 (p : Pattern) (guard : d181000 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180999 p = 1 := by simpa only [d181000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24226 p hg
    simpa only [d181000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24228 (p : Pattern) (guard : d181001 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180994 p = 1 := by simpa only [d181001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24221 p hg
    simpa only [d181001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181000 p = 1 := by simpa only [d181001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24227 p hg
    simpa only [d181001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24229 (p : Pattern) (guard : d181002 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181001 p = 1 := by simpa only [d181002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24228 p hg
    simpa only [d181002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24230 (p : Pattern) (guard : d181003 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181002 p = 1 := by simpa only [d181003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24229 p hg
    simpa only [d181003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24231 (p : Pattern) (guard : d181004 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181004, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181004, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181003 p = 1 := by simpa only [d181004, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24230 p hg
    simpa only [d181004, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24232 (p : Pattern) (guard : d181005 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181004 p = 1 := by simpa only [d181005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24231 p hg
    simpa only [d181005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24233 (p : Pattern) (guard : d181006 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180925 p = 1 := by simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24145 p hg
    simpa only [d181006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24234 (p : Pattern) (guard : d181007 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181006 p = 1 := by simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24233 p hg
    simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24235 (p : Pattern) (guard : d181008 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181007 p = 1 := by simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24234 p hg
    simpa only [d181008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24236 (p : Pattern) (guard : d181009 p = 1) : d48706 p ≤ (3 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181008 p = 1 := by simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24235 p hg
    simpa only [d181009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24237 (p : Pattern) (guard : d181010 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181009 p = 1 := by simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24236 p hg
    simpa only [d181010, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24238 (p : Pattern) (guard : d181011 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181010 p = 1 := by simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24237 p hg
    simpa only [d181011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24239 (p : Pattern) (guard : d181012 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181005 p = 1 := by simpa only [d181012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24232 p hg
    simpa only [d181012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181011 p = 1 := by simpa only [d181012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24238 p hg
    simpa only [d181012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24240 (p : Pattern) (guard : d181013 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181012 p = 1 := by simpa only [d181013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24239 p hg
    simpa only [d181013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24241 (p : Pattern) (guard : d181014 p = 1) : d48707 p ≤ (3 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181013 p = 1 := by simpa only [d181014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24240 p hg
    simpa only [d181014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d181014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24242 (p : Pattern) (guard : d181015 p = 1) : d48748 p ≤ (3 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181014 p = 1 := by simpa only [d181015, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24241 p hg
    simpa only [d181015, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181015, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d181015, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24243 (p : Pattern) (guard : d181016 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181016, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d181016, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181015 p = 1 := by simpa only [d181016, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24242 p hg
    simpa only [d181016, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24244 (p : Pattern) (guard : d181017 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181016 p = 1 := by simpa only [d181017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24243 p hg
    simpa only [d181017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24245 (p : Pattern) (guard : d181018 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181017 p = 1 := by simpa only [d181018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24244 p hg
    simpa only [d181018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24246 (p : Pattern) (guard : d181019 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181018 p = 1 := by simpa only [d181019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24245 p hg
    simpa only [d181019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24247 (p : Pattern) (guard : d181020 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181019 p = 1 := by simpa only [d181020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24246 p hg
    simpa only [d181020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24248 (p : Pattern) (guard : d181021 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d181021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181020 p = 1 := by simpa only [d181021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24247 p hg
    simpa only [d181021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24249 (p : Pattern) (guard : d181022 p = 1) : d48749 p ≤ (3 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d180973 p = 1 := by simpa only [d181022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24196 p hg
    simpa only [d181022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181021 p = 1 := by simpa only [d181022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24248 p hg
    simpa only [d181022, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
