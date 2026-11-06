import NetHack.Soko22Hazard87.Compare179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45000 (p : Pattern) (guard : d367273 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367232 p = 1 := by simpa only [d367273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d367273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45001 (p : Pattern) (guard : d367274 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367234 p = 1 := by simpa only [d367274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44927 p hg
    simpa only [d367274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45002 (p : Pattern) (guard : d367275 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367273 p = 1 := by simpa only [d367275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45000 p hg
    simpa only [d367275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367274 p = 1 := by simpa only [d367275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45001 p hg
    simpa only [d367275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45003 (p : Pattern) (guard : d367276 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367275 p = 1 := by simpa only [d367276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45002 p hg
    simpa only [d367276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45004 (p : Pattern) (guard : d367277 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367276 p = 1 := by simpa only [d367277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45003 p hg
    simpa only [d367277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45005 (p : Pattern) (guard : d367278 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367277 p = 1 := by simpa only [d367278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45004 p hg
    simpa only [d367278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45006 (p : Pattern) (guard : d367279 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367241 p = 1 := by simpa only [d367279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44934 p hg
    simpa only [d367279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45007 (p : Pattern) (guard : d367280 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367244 p = 1 := by simpa only [d367280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44937 p hg
    simpa only [d367280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45008 (p : Pattern) (guard : d367281 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367279 p = 1 := by simpa only [d367281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45006 p hg
    simpa only [d367281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367280 p = 1 := by simpa only [d367281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45007 p hg
    simpa only [d367281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45009 (p : Pattern) (guard : d367282 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367281 p = 1 := by simpa only [d367282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45008 p hg
    simpa only [d367282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45010 (p : Pattern) (guard : d367283 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367282 p = 1 := by simpa only [d367283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45009 p hg
    simpa only [d367283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45011 (p : Pattern) (guard : d367284 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367259 p = 1 := by simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44953 p hg
    simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45012 (p : Pattern) (guard : d367285 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367284 p = 1 := by simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45011 p hg
    simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367221 p = 1 := by simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44914 p hg
    simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45013 (p : Pattern) (guard : d367286 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367285 p = 1 := by simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45012 p hg
    simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45014 (p : Pattern) (guard : d367287 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367265 p = 1 := by simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44959 p hg
    simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45015 (p : Pattern) (guard : d367288 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367287 p = 1 := by simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45014 p hg
    simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45016 (p : Pattern) (guard : d367289 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367288 p = 1 := by simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45015 p hg
    simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45017 (p : Pattern) (guard : d367290 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367286 p = 1 := by simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45013 p hg
    simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367289 p = 1 := by simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45016 p hg
    simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45018 (p : Pattern) (guard : d367291 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d367283 p = 1 := by simpa only [d367291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45010 p hg
    simpa only [d367291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367290 p = 1 := by simpa only [d367291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45017 p hg
    simpa only [d367291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45019 (p : Pattern) (guard : d367292 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d367278 p = 1 := by simpa only [d367292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45005 p hg
    simpa only [d367292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367291 p = 1 := by simpa only [d367292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45018 p hg
    simpa only [d367292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45020 (p : Pattern) (guard : d367293 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d367271 p = 1 := by simpa only [d367293, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44999 p hg
    simpa only [d367293, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367292 p = 1 := by simpa only [d367293, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45019 p hg
    simpa only [d367293, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45021 (p : Pattern) (guard : d367294 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d367272 p = 1 := by simpa only [d367294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44966 p hg
    simpa only [d367294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367293 p = 1 := by simpa only [d367294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45020 p hg
    simpa only [d367294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45022 (p : Pattern) (guard : d367295 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367212 p = 1 := by simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44890 p hg
    simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45023 (p : Pattern) (guard : d367296 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367295 p = 1 := by simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45022 p hg
    simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45024 (p : Pattern) (guard : d367297 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367296 p = 1 := by simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45023 p hg
    simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45025 (p : Pattern) (guard : d367298 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367297 p = 1 := by simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45024 p hg
    simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45026 (p : Pattern) (guard : d367299 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367298 p = 1 := by simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45025 p hg
    simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45027 (p : Pattern) (guard : d367300 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d367217 p = 1 := by simpa only [d367300, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44913 p hg
    simpa only [d367300, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367299 p = 1 := by simpa only [d367300, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45026 p hg
    simpa only [d367300, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45028 (p : Pattern) (guard : d367295 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367212 p = 1 := by simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44908 p hg
    simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45029 (p : Pattern) (guard : d367296 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367295 p = 1 := by simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45028 p hg
    simpa only [d367296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45030 (p : Pattern) (guard : d367297 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367296 p = 1 := by simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45029 p hg
    simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45031 (p : Pattern) (guard : d367298 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367297 p = 1 := by simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45030 p hg
    simpa only [d367298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45032 (p : Pattern) (guard : d367299 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367298 p = 1 := by simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45031 p hg
    simpa only [d367299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45033 (p : Pattern) (guard : d367301 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367222 p = 1 := by simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44915 p hg
    simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45034 (p : Pattern) (guard : d367302 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367301 p = 1 := by simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45033 p hg
    simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45035 (p : Pattern) (guard : d367303 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367302 p = 1 := by simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45034 p hg
    simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45036 (p : Pattern) (guard : d367304 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367303 p = 1 := by simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45035 p hg
    simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45037 (p : Pattern) (guard : d367305 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367304 p = 1 := by simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45036 p hg
    simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45038 (p : Pattern) (guard : d367306 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d367299 p = 1 := by simpa only [d367306, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45032 p hg
    simpa only [d367306, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367305 p = 1 := by simpa only [d367306, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45037 p hg
    simpa only [d367306, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45039 (p : Pattern) (guard : d367307 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d367300 p = 1 := by simpa only [d367307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45027 p hg
    simpa only [d367307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367306 p = 1 := by simpa only [d367307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45038 p hg
    simpa only [d367307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45040 (p : Pattern) (guard : d367308 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367294 p = 1 := by simpa only [d367308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45021 p hg
    simpa only [d367308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367307 p = 1 := by simpa only [d367308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45039 p hg
    simpa only [d367308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45041 (p : Pattern) (guard : d367309 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367308 p = 1 := by simpa only [d367309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45040 p hg
    simpa only [d367309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d367309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45042 (p : Pattern) (guard : d367310 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367231 p = 1 := by simpa only [d367310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44924 p hg
    simpa only [d367310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367309 p = 1 := by simpa only [d367310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45041 p hg
    simpa only [d367310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45043 (p : Pattern) (guard : d44446 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45044 (p : Pattern) (guard : d44447 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44446 p = 1 := by simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45043 p hg
    simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45045 (p : Pattern) (guard : d44448 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44447 p = 1 := by simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45044 p hg
    simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45046 (p : Pattern) (guard : d44449 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44448 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45045 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45047 (p : Pattern) (guard : d44535 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44449 p = 1 := by simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45046 p hg
    simpa only [d44535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45048 (p : Pattern) (guard : d44611 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45049 (p : Pattern) (guard : d44612 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44611 p = 1 := by simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45048 p hg
    simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45050 (p : Pattern) (guard : d44613 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44612 p = 1 := by simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45049 p hg
    simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45051 (p : Pattern) (guard : d367186 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44448 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45045 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44613 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45050 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45052 (p : Pattern) (guard : d367187 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44449 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45046 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367186 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45051 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45053 (p : Pattern) (guard : d367249 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d44535 p = 1 := by simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45047 p hg
    simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367187 p = 1 := by simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45052 p hg
    simpa only [d367249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45054 (p : Pattern) (guard : d367250 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367250, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d367250, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367249 p = 1 := by simpa only [d367250, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45053 p hg
    simpa only [d367250, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45055 (p : Pattern) (guard : d367251 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367251, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d367251, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367250 p = 1 := by simpa only [d367251, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45054 p hg
    simpa only [d367251, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45056 (p : Pattern) (guard : d44614 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44613 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45050 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45057 (p : Pattern) (guard : d367188 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367186 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45051 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44614 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45056 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45058 (p : Pattern) (guard : d367189 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367187 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45052 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367188 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45057 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45059 (p : Pattern) (guard : d367190 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367189 p = 1 := by simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45058 p hg
    simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45060 (p : Pattern) (guard : d367191 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367190 p = 1 := by simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45059 p hg
    simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45061 (p : Pattern) (guard : d367252 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367251 p = 1 := by simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45055 p hg
    simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367191 p = 1 := by simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45060 p hg
    simpa only [d367252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45062 (p : Pattern) (guard : d44616 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44614 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45056 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45063 (p : Pattern) (guard : d367192 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367188 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45057 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44616 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45062 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45064 (p : Pattern) (guard : d367193 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367192 p = 1 := by simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45063 p hg
    simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45065 (p : Pattern) (guard : d367194 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367193 p = 1 := by simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45064 p hg
    simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45066 (p : Pattern) (guard : d367195 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367191 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45060 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367194 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45065 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45067 (p : Pattern) (guard : d367253 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367252 p = 1 := by simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45061 p hg
    simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367195 p = 1 := by simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45066 p hg
    simpa only [d367253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45068 (p : Pattern) (guard : d367254 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367253 p = 1 := by simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45067 p hg
    simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d367254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45069 (p : Pattern) (guard : d367255 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367254 p = 1 := by simpa only [d367255, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45068 p hg
    simpa only [d367255, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367255, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d367255, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45070 (p : Pattern) (guard : d367256 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367256, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d367256, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367255 p = 1 := by simpa only [d367256, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45069 p hg
    simpa only [d367256, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45071 (p : Pattern) (guard : d367196 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367194 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45065 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45072 (p : Pattern) (guard : d367197 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367195 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45066 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367196 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45071 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45073 (p : Pattern) (guard : d367198 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367197 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45072 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45074 (p : Pattern) (guard : d367199 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367198 p = 1 := by simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45073 p hg
    simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45075 (p : Pattern) (guard : d367200 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367199 p = 1 := by simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45074 p hg
    simpa only [d367200, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45076 (p : Pattern) (guard : d367257 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367256 p = 1 := by simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45070 p hg
    simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367200 p = 1 := by simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45075 p hg
    simpa only [d367257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45077 (p : Pattern) (guard : d367258 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367257 p = 1 := by simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45076 p hg
    simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45078 (p : Pattern) (guard : d367259 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367258 p = 1 := by simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45077 p hg
    simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45079 (p : Pattern) (guard : d367284 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367259 p = 1 := by simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45078 p hg
    simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45080 (p : Pattern) (guard : d367201 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367196 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45071 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45081 (p : Pattern) (guard : d367202 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367201 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45080 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45082 (p : Pattern) (guard : d367203 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367202 p = 1 := by simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45081 p hg
    simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d367203, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45083 (p : Pattern) (guard : d367204 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367203 p = 1 := by simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45082 p hg
    simpa only [d367204, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45084 (p : Pattern) (guard : d367205 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45075 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367204 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45083 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45085 (p : Pattern) (guard : d367206 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367205 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45084 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45086 (p : Pattern) (guard : d367207 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367206 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45085 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45087 (p : Pattern) (guard : d367221 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367207 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45086 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45088 (p : Pattern) (guard : d367285 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367284 p = 1 := by simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45079 p hg
    simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367221 p = 1 := by simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45087 p hg
    simpa only [d367285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45089 (p : Pattern) (guard : d367286 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367285 p = 1 := by simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45088 p hg
    simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45090 (p : Pattern) (guard : d367263 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45075 p hg
    simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45091 (p : Pattern) (guard : d367264 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367263 p = 1 := by simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45090 p hg
    simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45092 (p : Pattern) (guard : d367265 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367264 p = 1 := by simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45091 p hg
    simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45093 (p : Pattern) (guard : d367287 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367265 p = 1 := by simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45092 p hg
    simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45094 (p : Pattern) (guard : d367288 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367287 p = 1 := by simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45093 p hg
    simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45095 (p : Pattern) (guard : d367289 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367288 p = 1 := by simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45094 p hg
    simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45096 (p : Pattern) (guard : d367290 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367286 p = 1 := by simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45089 p hg
    simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367289 p = 1 := by simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45095 p hg
    simpa only [d367290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45097 (p : Pattern) (guard : d367311 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367290 p = 1 := by simpa only [d367311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45096 p hg
    simpa only [d367311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45098 (p : Pattern) (guard : d367312 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367311 p = 1 := by simpa only [d367312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45097 p hg
    simpa only [d367312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45099 (p : Pattern) (guard : d367313 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367313, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367313, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367312 p = 1 := by simpa only [d367313, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45098 p hg
    simpa only [d367313, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45100 (p : Pattern) (guard : d367314 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367313 p = 1 := by simpa only [d367314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45099 p hg
    simpa only [d367314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45101 (p : Pattern) (guard : d367209 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367204 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45083 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45102 (p : Pattern) (guard : d367210 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367209 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45101 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45103 (p : Pattern) (guard : d367211 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367210 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45102 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45104 (p : Pattern) (guard : d367222 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367211 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45103 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45105 (p : Pattern) (guard : d367301 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367222 p = 1 := by simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45104 p hg
    simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45106 (p : Pattern) (guard : d367302 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367301 p = 1 := by simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45105 p hg
    simpa only [d367302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45107 (p : Pattern) (guard : d367303 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367302 p = 1 := by simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45106 p hg
    simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45108 (p : Pattern) (guard : d367304 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367303 p = 1 := by simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45107 p hg
    simpa only [d367304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45109 (p : Pattern) (guard : d367305 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367304 p = 1 := by simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45108 p hg
    simpa only [d367305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45110 (p : Pattern) (guard : d367315 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367315, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367315, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367305 p = 1 := by simpa only [d367315, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45109 p hg
    simpa only [d367315, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45111 (p : Pattern) (guard : d367316 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367315 p = 1 := by simpa only [d367316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45110 p hg
    simpa only [d367316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45112 (p : Pattern) (guard : d367317 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367314 p = 1 := by simpa only [d367317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45100 p hg
    simpa only [d367317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367316 p = 1 := by simpa only [d367317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45111 p hg
    simpa only [d367317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45113 (p : Pattern) (guard : d367318 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367317 p = 1 := by simpa only [d367318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45112 p hg
    simpa only [d367318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45114 (p : Pattern) (guard : d367319 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367318 p = 1 := by simpa only [d367319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45113 p hg
    simpa only [d367319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d367319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45115 (p : Pattern) (guard : d367320 p = 1) : d51470 p ≤ (8 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367310 p = 1 := by simpa only [d367320, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45042 p hg
    simpa only [d367320, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367319 p = 1 := by simpa only [d367320, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45114 p hg
    simpa only [d367320, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45116 (p : Pattern) (guard : d35372 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32698 p = 1 := by simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44167 p hg
    simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45117 (p : Pattern) (guard : d2006 p = 1) : d51183 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43393 p hg
    simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44693 p hg
    simpa only [d2006, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45118 (p : Pattern) (guard : d10054 p = 1) : d51186 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45117 p hg
    simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44695 p hg
    simpa only [d10054, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45119 (p : Pattern) (guard : d10055 p = 1) : d51186 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45118 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45120 (p : Pattern) (guard : d35373 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d35372 p = 1 := by simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45116 p hg
    simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45119 p hg
    simpa only [d35373, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45121 (p : Pattern) (guard : d44441 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d35373 p = 1 := by simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45120 p hg
    simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45122 (p : Pattern) (guard : d44442 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d44441 p = 1 := by simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45121 p hg
    simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45123 (p : Pattern) (guard : d44443 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d44442 p = 1 := by simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45122 p hg
    simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d44443, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45124 (p : Pattern) (guard : d44444 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44443 p = 1 := by simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45123 p hg
    simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45125 (p : Pattern) (guard : d44686 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44444 p = 1 := by simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45124 p hg
    simpa only [d44686, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45126 (p : Pattern) (guard : d44445 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare45127 (p : Pattern) (guard : d44687 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d44686 p = 1 := by simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45125 p hg
    simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44445 p = 1 := by simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45126 p hg
    simpa only [d44687, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45128 (p : Pattern) (guard : d44446 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45129 (p : Pattern) (guard : d44688 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d44687 p = 1 := by simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45127 p hg
    simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44446 p = 1 := by simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45128 p hg
    simpa only [d44688, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45130 (p : Pattern) (guard : d44689 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44688 p = 1 := by simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45129 p hg
    simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d44689, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45131 (p : Pattern) (guard : d44690 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44689 p = 1 := by simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45130 p hg
    simpa only [d44690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45132 (p : Pattern) (guard : d44691 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d44691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44690 p = 1 := by simpa only [d44691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45131 p hg
    simpa only [d44691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45133 (p : Pattern) (guard : d44609 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d44443 p = 1 := by simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45123 p hg
    simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45134 (p : Pattern) (guard : d44784 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44609 p = 1 := by simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45133 p hg
    simpa only [d44784, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45135 (p : Pattern) (guard : d44610 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare45136 (p : Pattern) (guard : d44785 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d44784 p = 1 := by simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45134 p hg
    simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44610 p = 1 := by simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45135 p hg
    simpa only [d44785, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45137 (p : Pattern) (guard : d44611 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45138 (p : Pattern) (guard : d44786 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d44785 p = 1 := by simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45136 p hg
    simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44611 p = 1 := by simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45137 p hg
    simpa only [d44786, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45139 (p : Pattern) (guard : d44787 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44786 p = 1 := by simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45138 p hg
    simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d44787, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45140 (p : Pattern) (guard : d367321 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44689 p = 1 := by simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45130 p hg
    simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44787 p = 1 := by simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45139 p hg
    simpa only [d367321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45141 (p : Pattern) (guard : d367322 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44690 p = 1 := by simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45131 p hg
    simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367321 p = 1 := by simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45140 p hg
    simpa only [d367322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45142 (p : Pattern) (guard : d367323 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d44691 p = 1 := by simpa only [d367323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45132 p hg
    simpa only [d367323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367322 p = 1 := by simpa only [d367323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45141 p hg
    simpa only [d367323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45143 (p : Pattern) (guard : d367324 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367324, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d367324, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367323 p = 1 := by simpa only [d367324, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45142 p hg
    simpa only [d367324, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45144 (p : Pattern) (guard : d367325 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367325, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d367325, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367324 p = 1 := by simpa only [d367325, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45143 p hg
    simpa only [d367325, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45145 (p : Pattern) (guard : d44788 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44787 p = 1 := by simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45139 p hg
    simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d44788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45146 (p : Pattern) (guard : d367326 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367321 p = 1 := by simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45140 p hg
    simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44788 p = 1 := by simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45145 p hg
    simpa only [d367326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45147 (p : Pattern) (guard : d367327 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367322 p = 1 := by simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45141 p hg
    simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367326 p = 1 := by simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45146 p hg
    simpa only [d367327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45148 (p : Pattern) (guard : d367328 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367327 p = 1 := by simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45147 p hg
    simpa only [d367328, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45149 (p : Pattern) (guard : d367329 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367328 p = 1 := by simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45148 p hg
    simpa only [d367329, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45150 (p : Pattern) (guard : d367330 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367325 p = 1 := by simpa only [d367330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45144 p hg
    simpa only [d367330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367329 p = 1 := by simpa only [d367330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45149 p hg
    simpa only [d367330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45151 (p : Pattern) (guard : d44790 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44788 p = 1 := by simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45145 p hg
    simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d44790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45152 (p : Pattern) (guard : d367331 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367326 p = 1 := by simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45146 p hg
    simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44790 p = 1 := by simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45151 p hg
    simpa only [d367331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45153 (p : Pattern) (guard : d367332 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367331 p = 1 := by simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45152 p hg
    simpa only [d367332, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45154 (p : Pattern) (guard : d367333 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367332 p = 1 := by simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45153 p hg
    simpa only [d367333, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45155 (p : Pattern) (guard : d367334 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367329 p = 1 := by simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45149 p hg
    simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367333 p = 1 := by simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45154 p hg
    simpa only [d367334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45156 (p : Pattern) (guard : d367335 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367330 p = 1 := by simpa only [d367335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45150 p hg
    simpa only [d367335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367334 p = 1 := by simpa only [d367335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45155 p hg
    simpa only [d367335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45157 (p : Pattern) (guard : d367336 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367335 p = 1 := by simpa only [d367336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45156 p hg
    simpa only [d367336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45158 (p : Pattern) (guard : d367337 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367336 p = 1 := by simpa only [d367337, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45157 p hg
    simpa only [d367337, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367337, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d367337, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45159 (p : Pattern) (guard : d367338 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367338, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367338, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367337 p = 1 := by simpa only [d367338, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45158 p hg
    simpa only [d367338, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45160 (p : Pattern) (guard : d367339 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367333 p = 1 := by simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45154 p hg
    simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45161 (p : Pattern) (guard : d367340 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367334 p = 1 := by simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45155 p hg
    simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367339 p = 1 := by simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d367340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45162 (p : Pattern) (guard : d367341 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367340 p = 1 := by simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45161 p hg
    simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45163 (p : Pattern) (guard : d367342 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367341 p = 1 := by simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45162 p hg
    simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d367342, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45164 (p : Pattern) (guard : d367343 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367342 p = 1 := by simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45163 p hg
    simpa only [d367343, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45165 (p : Pattern) (guard : d367344 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367338 p = 1 := by simpa only [d367344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45159 p hg
    simpa only [d367344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367343 p = 1 := by simpa only [d367344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d367344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45166 (p : Pattern) (guard : d367345 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367344 p = 1 := by simpa only [d367345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45165 p hg
    simpa only [d367345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45167 (p : Pattern) (guard : d367346 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367345 p = 1 := by simpa only [d367346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45166 p hg
    simpa only [d367346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45168 (p : Pattern) (guard : d367347 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367346 p = 1 := by simpa only [d367347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45167 p hg
    simpa only [d367347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45169 (p : Pattern) (guard : d367348 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367339 p = 1 := by simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45170 (p : Pattern) (guard : d367349 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367348 p = 1 := by simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45169 p hg
    simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d367349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45171 (p : Pattern) (guard : d367350 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367349 p = 1 := by simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45170 p hg
    simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d367350, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45172 (p : Pattern) (guard : d367351 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367350 p = 1 := by simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45171 p hg
    simpa only [d367351, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45173 (p : Pattern) (guard : d367352 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367343 p = 1 := by simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367351 p = 1 := by simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45172 p hg
    simpa only [d367352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45174 (p : Pattern) (guard : d367353 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367352 p = 1 := by simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45173 p hg
    simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45175 (p : Pattern) (guard : d367354 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367353 p = 1 := by simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45174 p hg
    simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45176 (p : Pattern) (guard : d367355 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367354 p = 1 := by simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45175 p hg
    simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45177 (p : Pattern) (guard : d367356 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367347 p = 1 := by simpa only [d367356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45168 p hg
    simpa only [d367356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367355 p = 1 := by simpa only [d367356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d367356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45178 (p : Pattern) (guard : d367357 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367356 p = 1 := by simpa only [d367357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45177 p hg
    simpa only [d367357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45179 (p : Pattern) (guard : d367358 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367343 p = 1 := by simpa only [d367358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d367358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45180 (p : Pattern) (guard : d367359 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367358 p = 1 := by simpa only [d367359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45179 p hg
    simpa only [d367359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45181 (p : Pattern) (guard : d367360 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367359 p = 1 := by simpa only [d367360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45180 p hg
    simpa only [d367360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45182 (p : Pattern) (guard : d367361 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367360 p = 1 := by simpa only [d367361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45181 p hg
    simpa only [d367361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45183 (p : Pattern) (guard : d367362 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367361 p = 1 := by simpa only [d367362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45182 p hg
    simpa only [d367362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45184 (p : Pattern) (guard : d367363 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367362 p = 1 := by simpa only [d367363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45183 p hg
    simpa only [d367363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45185 (p : Pattern) (guard : d367364 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367357 p = 1 := by simpa only [d367364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45178 p hg
    simpa only [d367364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367363 p = 1 := by simpa only [d367364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45184 p hg
    simpa only [d367364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45186 (p : Pattern) (guard : d367365 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367364 p = 1 := by simpa only [d367365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45185 p hg
    simpa only [d367365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45187 (p : Pattern) (guard : d367366 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367365 p = 1 := by simpa only [d367366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45186 p hg
    simpa only [d367366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45188 (p : Pattern) (guard : d367367 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367367, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367367, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367366 p = 1 := by simpa only [d367367, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45187 p hg
    simpa only [d367367, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45189 (p : Pattern) (guard : d367368 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367367 p = 1 := by simpa only [d367368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45188 p hg
    simpa only [d367368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45190 (p : Pattern) (guard : d367369 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367351 p = 1 := by simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45172 p hg
    simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45191 (p : Pattern) (guard : d367370 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367369 p = 1 := by simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45190 p hg
    simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45192 (p : Pattern) (guard : d367371 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367370 p = 1 := by simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45191 p hg
    simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45193 (p : Pattern) (guard : d367372 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367371 p = 1 := by simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45192 p hg
    simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45194 (p : Pattern) (guard : d367373 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367372 p = 1 := by simpa only [d367373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45193 p hg
    simpa only [d367373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45195 (p : Pattern) (guard : d367374 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367373 p = 1 := by simpa only [d367374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45194 p hg
    simpa only [d367374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45196 (p : Pattern) (guard : d367375 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367374 p = 1 := by simpa only [d367375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45195 p hg
    simpa only [d367375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45197 (p : Pattern) (guard : d367376 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367375 p = 1 := by simpa only [d367376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45196 p hg
    simpa only [d367376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45198 (p : Pattern) (guard : d367377 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d367377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367376 p = 1 := by simpa only [d367377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45197 p hg
    simpa only [d367377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45199 (p : Pattern) (guard : d367378 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367378, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367378, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367377 p = 1 := by simpa only [d367378, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45198 p hg
    simpa only [d367378, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45200 (p : Pattern) (guard : d367379 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367378 p = 1 := by simpa only [d367379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45199 p hg
    simpa only [d367379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45201 (p : Pattern) (guard : d367380 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367368 p = 1 := by simpa only [d367380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45189 p hg
    simpa only [d367380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367379 p = 1 := by simpa only [d367380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45200 p hg
    simpa only [d367380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45202 (p : Pattern) (guard : d367381 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367380 p = 1 := by simpa only [d367381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45201 p hg
    simpa only [d367381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45203 (p : Pattern) (guard : d367382 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367381 p = 1 := by simpa only [d367382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45202 p hg
    simpa only [d367382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d367382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45204 (p : Pattern) (guard : d367383 p = 1) : d51634 p ≤ (8 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367382 p = 1 := by simpa only [d367383, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45203 p hg
    simpa only [d367383, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367383, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d367383, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45205 (p : Pattern) (guard : d367384 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d367320 p = 1 := by simpa only [d367384, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45115 p hg
    simpa only [d367384, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367383 p = 1 := by simpa only [d367384, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45204 p hg
    simpa only [d367384, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45206 (p : Pattern) (guard : d367385 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367384 p = 1 := by simpa only [d367385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45205 p hg
    simpa only [d367385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45207 (p : Pattern) (guard : d367386 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367385 p = 1 := by simpa only [d367386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45206 p hg
    simpa only [d367386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45208 (p : Pattern) (guard : d367387 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367386 p = 1 := by simpa only [d367387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45207 p hg
    simpa only [d367387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45209 (p : Pattern) (guard : d367388 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367387 p = 1 := by simpa only [d367388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45208 p hg
    simpa only [d367388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45210 (p : Pattern) (guard : d367389 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367388 p = 1 := by simpa only [d367389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45209 p hg
    simpa only [d367389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45211 (p : Pattern) (guard : d367390 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367389 p = 1 := by simpa only [d367390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45210 p hg
    simpa only [d367390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45212 (p : Pattern) (guard : d367391 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367390 p = 1 := by simpa only [d367391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45211 p hg
    simpa only [d367391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45213 (p : Pattern) (guard : d367392 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367391 p = 1 := by simpa only [d367392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45212 p hg
    simpa only [d367392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45214 (p : Pattern) (guard : d367393 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367392 p = 1 := by simpa only [d367393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45213 p hg
    simpa only [d367393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45215 (p : Pattern) (guard : d367394 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367393 p = 1 := by simpa only [d367394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45214 p hg
    simpa only [d367394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45216 (p : Pattern) (guard : d367395 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d367185 p = 1 := by simpa only [d367395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44854 p hg
    simpa only [d367395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367394 p = 1 := by simpa only [d367395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45215 p hg
    simpa only [d367395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45217 (p : Pattern) (guard : d367396 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 260 with
  | false =>
    have hg : d367395 p = 1 := by simpa only [d367396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45216 p hg
    simpa only [d367396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45218 (p : Pattern) (guard : d367397 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 259 with
  | false =>
    have hg : d367396 p = 1 := by simpa only [d367397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45217 p hg
    simpa only [d367397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45219 (p : Pattern) (guard : d367398 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 258 with
  | false =>
    have hg : d367397 p = 1 := by simpa only [d367398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45218 p hg
    simpa only [d367398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45220 (p : Pattern) (guard : d367399 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 257 with
  | false =>
    have hg : d367398 p = 1 := by simpa only [d367399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45219 p hg
    simpa only [d367399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45221 (p : Pattern) (guard : d367400 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 256 with
  | false =>
    have hg : d367399 p = 1 := by simpa only [d367400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45220 p hg
    simpa only [d367400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45222 (p : Pattern) (guard : d367401 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 255 with
  | false =>
    have hg : d367400 p = 1 := by simpa only [d367401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45221 p hg
    simpa only [d367401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45223 (p : Pattern) (guard : d367402 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 254 with
  | false =>
    have hg : d367401 p = 1 := by simpa only [d367402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45222 p hg
    simpa only [d367402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45224 (p : Pattern) (guard : d367403 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 253 with
  | false =>
    have hg : d367402 p = 1 := by simpa only [d367403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45223 p hg
    simpa only [d367403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45225 (p : Pattern) (guard : d367404 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 252 with
  | false =>
    have hg : d367403 p = 1 := by simpa only [d367404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45224 p hg
    simpa only [d367404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45226 (p : Pattern) (guard : d367405 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 251 with
  | false =>
    have hg : d367404 p = 1 := by simpa only [d367405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45225 p hg
    simpa only [d367405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45227 (p : Pattern) (guard : d367406 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 250 with
  | false =>
    have hg : d367405 p = 1 := by simpa only [d367406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45226 p hg
    simpa only [d367406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45228 (p : Pattern) (guard : d367407 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 249 with
  | false =>
    have hg : d367406 p = 1 := by simpa only [d367407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45227 p hg
    simpa only [d367407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45229 (p : Pattern) (guard : d367408 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 245 with
  | false =>
    have hg : d367407 p = 1 := by simpa only [d367408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d367408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45230 (p : Pattern) (guard : d367409 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 200 with
  | false =>
    have hg : d367408 p = 1 := by simpa only [d367409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45229 p hg
    simpa only [d367409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45231 (p : Pattern) (guard : d367410 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 199 with
  | false =>
    have hg : d367409 p = 1 := by simpa only [d367410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45230 p hg
    simpa only [d367410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45232 (p : Pattern) (guard : d367411 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 186 with
  | false =>
    have hg : d367410 p = 1 := by simpa only [d367411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45231 p hg
    simpa only [d367411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45233 (p : Pattern) (guard : d367412 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 185 with
  | false =>
    have hg : d367411 p = 1 := by simpa only [d367412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45232 p hg
    simpa only [d367412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45234 (p : Pattern) (guard : d367413 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 184 with
  | false =>
    have hg : d367412 p = 1 := by simpa only [d367413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45233 p hg
    simpa only [d367413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45235 (p : Pattern) (guard : d367414 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 181 with
  | false =>
    have hg : d367413 p = 1 := by simpa only [d367414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45234 p hg
    simpa only [d367414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45236 (p : Pattern) (guard : d367415 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 177 with
  | false =>
    have hg : d367414 p = 1 := by simpa only [d367415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45235 p hg
    simpa only [d367415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45237 (p : Pattern) (guard : d367416 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 164 with
  | false =>
    have hg : d367415 p = 1 := by simpa only [d367416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45236 p hg
    simpa only [d367416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45238 (p : Pattern) (guard : d367417 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 156 with
  | false =>
    have hg : d367416 p = 1 := by simpa only [d367417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45237 p hg
    simpa only [d367417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45239 (p : Pattern) (guard : d367418 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 155 with
  | false =>
    have hg : d367417 p = 1 := by simpa only [d367418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45238 p hg
    simpa only [d367418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45240 (p : Pattern) (guard : d367419 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 134 with
  | false =>
    have hg : d367418 p = 1 := by simpa only [d367419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45239 p hg
    simpa only [d367419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45241 (p : Pattern) (guard : d367420 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 133 with
  | false =>
    have hg : d367419 p = 1 := by simpa only [d367420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45240 p hg
    simpa only [d367420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45242 (p : Pattern) (guard : d367421 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 120 with
  | false =>
    have hg : d367420 p = 1 := by simpa only [d367421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45241 p hg
    simpa only [d367421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45243 (p : Pattern) (guard : d367422 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 118 with
  | false =>
    have hg : d367421 p = 1 := by simpa only [d367422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45242 p hg
    simpa only [d367422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45244 (p : Pattern) (guard : d367423 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 114 with
  | false =>
    have hg : d367422 p = 1 := by simpa only [d367423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45243 p hg
    simpa only [d367423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45245 (p : Pattern) (guard : d367424 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 111 with
  | false =>
    have hg : d367423 p = 1 := by simpa only [d367424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45244 p hg
    simpa only [d367424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45246 (p : Pattern) (guard : d367425 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 98 with
  | false =>
    have hg : d367424 p = 1 := by simpa only [d367425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45245 p hg
    simpa only [d367425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45247 (p : Pattern) (guard : d367426 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 97 with
  | false =>
    have hg : d367425 p = 1 := by simpa only [d367426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45246 p hg
    simpa only [d367426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45248 (p : Pattern) (guard : d367427 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 94 with
  | false =>
    have hg : d367426 p = 1 := by simpa only [d367427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45247 p hg
    simpa only [d367427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45249 (p : Pattern) (guard : d367428 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 76 with
  | false =>
    have hg : d367427 p = 1 := by simpa only [d367428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45248 p hg
    simpa only [d367428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367428, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
