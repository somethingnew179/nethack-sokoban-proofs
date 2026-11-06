import NetHack.Soko22Hazard87.Compare168
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42250 (p : Pattern) (guard : d348902 p = 1) : d51077 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348901 p = 1 := by simpa only [d348902, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42249 p hg
    simpa only [d348902, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348902, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d348902, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42251 (p : Pattern) (guard : d348903 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348903, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348903, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348902 p = 1 := by simpa only [d348903, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42250 p hg
    simpa only [d348903, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42252 (p : Pattern) (guard : d348904 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348903 p = 1 := by simpa only [d348904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42251 p hg
    simpa only [d348904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42253 (p : Pattern) (guard : d348905 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348904 p = 1 := by simpa only [d348905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42252 p hg
    simpa only [d348905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42254 (p : Pattern) (guard : d348906 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348905 p = 1 := by simpa only [d348906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42253 p hg
    simpa only [d348906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42255 (p : Pattern) (guard : d348907 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348906 p = 1 := by simpa only [d348907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42254 p hg
    simpa only [d348907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42256 (p : Pattern) (guard : d348908 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348907 p = 1 := by simpa only [d348908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42255 p hg
    simpa only [d348908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42257 (p : Pattern) (guard : d348909 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348908 p = 1 := by simpa only [d348909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42256 p hg
    simpa only [d348909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42258 (p : Pattern) (guard : d348910 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348909 p = 1 := by simpa only [d348910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42257 p hg
    simpa only [d348910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42259 (p : Pattern) (guard : d348911 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348910 p = 1 := by simpa only [d348911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42258 p hg
    simpa only [d348911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42260 (p : Pattern) (guard : d348912 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348911 p = 1 := by simpa only [d348912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42259 p hg
    simpa only [d348912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42261 (p : Pattern) (guard : d348913 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348913, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348913, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348912 p = 1 := by simpa only [d348913, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42260 p hg
    simpa only [d348913, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42262 (p : Pattern) (guard : d348914 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348913 p = 1 := by simpa only [d348914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42261 p hg
    simpa only [d348914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42263 (p : Pattern) (guard : d348915 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348914 p = 1 := by simpa only [d348915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42262 p hg
    simpa only [d348915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42264 (p : Pattern) (guard : d348916 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348915 p = 1 := by simpa only [d348916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42263 p hg
    simpa only [d348916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42265 (p : Pattern) (guard : d348917 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348916 p = 1 := by simpa only [d348917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42264 p hg
    simpa only [d348917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42266 (p : Pattern) (guard : d348918 p = 1) : d51137 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d348917 p = 1 := by simpa only [d348918, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42265 p hg
    simpa only [d348918, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348918, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41676 p hg
    simpa only [d348918, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42267 (p : Pattern) (guard : d348919 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d348894 p = 1 := by simpa only [d348919, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42209 p hg
    simpa only [d348919, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348918 p = 1 := by simpa only [d348919, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42266 p hg
    simpa only [d348919, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42268 (p : Pattern) (guard : d348920 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348919 p = 1 := by simpa only [d348920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42267 p hg
    simpa only [d348920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42269 (p : Pattern) (guard : d348921 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348920 p = 1 := by simpa only [d348921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42268 p hg
    simpa only [d348921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42270 (p : Pattern) (guard : d348922 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348921 p = 1 := by simpa only [d348922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42269 p hg
    simpa only [d348922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42271 (p : Pattern) (guard : d348923 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348922 p = 1 := by simpa only [d348923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42270 p hg
    simpa only [d348923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42272 (p : Pattern) (guard : d348924 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348923 p = 1 := by simpa only [d348924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42271 p hg
    simpa only [d348924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42273 (p : Pattern) (guard : d348925 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348924 p = 1 := by simpa only [d348925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42272 p hg
    simpa only [d348925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42274 (p : Pattern) (guard : d348926 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348925 p = 1 := by simpa only [d348926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42273 p hg
    simpa only [d348926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42275 (p : Pattern) (guard : d348927 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348926 p = 1 := by simpa only [d348927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42274 p hg
    simpa only [d348927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42276 (p : Pattern) (guard : d348928 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348927 p = 1 := by simpa only [d348928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42275 p hg
    simpa only [d348928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42277 (p : Pattern) (guard : d348929 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348928 p = 1 := by simpa only [d348929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42276 p hg
    simpa only [d348929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42278 (p : Pattern) (guard : d348930 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d348858 p = 1 := by simpa only [d348930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42104 p hg
    simpa only [d348930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348929 p = 1 := by simpa only [d348930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42277 p hg
    simpa only [d348930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42279 (p : Pattern) (guard : d348931 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d348930 p = 1 := by simpa only [d348931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42278 p hg
    simpa only [d348931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42280 (p : Pattern) (guard : d348932 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d348931 p = 1 := by simpa only [d348932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42279 p hg
    simpa only [d348932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42281 (p : Pattern) (guard : d348933 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d348932 p = 1 := by simpa only [d348933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42280 p hg
    simpa only [d348933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42282 (p : Pattern) (guard : d348934 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d348933 p = 1 := by simpa only [d348934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42281 p hg
    simpa only [d348934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42283 (p : Pattern) (guard : d348935 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d348934 p = 1 := by simpa only [d348935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42282 p hg
    simpa only [d348935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42284 (p : Pattern) (guard : d348936 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d348935 p = 1 := by simpa only [d348936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42283 p hg
    simpa only [d348936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42285 (p : Pattern) (guard : d348937 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d348936 p = 1 := by simpa only [d348937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42284 p hg
    simpa only [d348937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42286 (p : Pattern) (guard : d348938 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d348937 p = 1 := by simpa only [d348938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42285 p hg
    simpa only [d348938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42287 (p : Pattern) (guard : d348939 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d348938 p = 1 := by simpa only [d348939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42286 p hg
    simpa only [d348939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42288 (p : Pattern) (guard : d348940 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d348939 p = 1 := by simpa only [d348940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42287 p hg
    simpa only [d348940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42289 (p : Pattern) (guard : d348941 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d348940 p = 1 := by simpa only [d348941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42288 p hg
    simpa only [d348941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42290 (p : Pattern) (guard : d348942 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d348941 p = 1 := by simpa only [d348942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42289 p hg
    simpa only [d348942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42291 (p : Pattern) (guard : d348943 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d348942 p = 1 := by simpa only [d348943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42290 p hg
    simpa only [d348943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42292 (p : Pattern) (guard : d348944 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d348943 p = 1 := by simpa only [d348944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42291 p hg
    simpa only [d348944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42293 (p : Pattern) (guard : d348945 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d348944 p = 1 := by simpa only [d348945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42292 p hg
    simpa only [d348945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42294 (p : Pattern) (guard : d348946 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d348945 p = 1 := by simpa only [d348946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42293 p hg
    simpa only [d348946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42295 (p : Pattern) (guard : d348947 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d348946 p = 1 := by simpa only [d348947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42294 p hg
    simpa only [d348947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42296 (p : Pattern) (guard : d348948 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d348947 p = 1 := by simpa only [d348948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42295 p hg
    simpa only [d348948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42297 (p : Pattern) (guard : d348949 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d348948 p = 1 := by simpa only [d348949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42296 p hg
    simpa only [d348949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42298 (p : Pattern) (guard : d348950 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d348949 p = 1 := by simpa only [d348950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42297 p hg
    simpa only [d348950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42299 (p : Pattern) (guard : d348951 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d348950 p = 1 := by simpa only [d348951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42298 p hg
    simpa only [d348951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42300 (p : Pattern) (guard : d348952 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d348951 p = 1 := by simpa only [d348952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42299 p hg
    simpa only [d348952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42301 (p : Pattern) (guard : d348953 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d348952 p = 1 := by simpa only [d348953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42300 p hg
    simpa only [d348953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42302 (p : Pattern) (guard : d348954 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d348953 p = 1 := by simpa only [d348954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42301 p hg
    simpa only [d348954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42303 (p : Pattern) (guard : d348955 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d348954 p = 1 := by simpa only [d348955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42302 p hg
    simpa only [d348955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42304 (p : Pattern) (guard : d348956 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d348955 p = 1 := by simpa only [d348956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42303 p hg
    simpa only [d348956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42305 (p : Pattern) (guard : d348957 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d348956 p = 1 := by simpa only [d348957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42304 p hg
    simpa only [d348957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42306 (p : Pattern) (guard : d348958 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d348957 p = 1 := by simpa only [d348958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42305 p hg
    simpa only [d348958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42307 (p : Pattern) (guard : d348959 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d348958 p = 1 := by simpa only [d348959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42306 p hg
    simpa only [d348959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42308 (p : Pattern) (guard : d348960 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d348959 p = 1 := by simpa only [d348960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42307 p hg
    simpa only [d348960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42309 (p : Pattern) (guard : d348961 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d348960 p = 1 := by simpa only [d348961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42308 p hg
    simpa only [d348961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42310 (p : Pattern) (guard : d348962 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d348961 p = 1 := by simpa only [d348962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42309 p hg
    simpa only [d348962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42311 (p : Pattern) (guard : d348963 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d348962 p = 1 := by simpa only [d348963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42310 p hg
    simpa only [d348963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42312 (p : Pattern) (guard : d348964 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d348963 p = 1 := by simpa only [d348964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42311 p hg
    simpa only [d348964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42313 (p : Pattern) (guard : d348965 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d348964 p = 1 := by simpa only [d348965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42312 p hg
    simpa only [d348965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42314 (p : Pattern) (guard : d348966 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d348965 p = 1 := by simpa only [d348966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42313 p hg
    simpa only [d348966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42315 (p : Pattern) (guard : d348967 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d348966 p = 1 := by simpa only [d348967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42314 p hg
    simpa only [d348967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42316 (p : Pattern) (guard : d348968 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d348967 p = 1 := by simpa only [d348968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42315 p hg
    simpa only [d348968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42317 (p : Pattern) (guard : d348969 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d348968 p = 1 := by simpa only [d348969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42316 p hg
    simpa only [d348969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42318 (p : Pattern) (guard : d348970 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d348969 p = 1 := by simpa only [d348970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42317 p hg
    simpa only [d348970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42319 (p : Pattern) (guard : d348971 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d348970 p = 1 := by simpa only [d348971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42318 p hg
    simpa only [d348971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42320 (p : Pattern) (guard : d348972 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d348971 p = 1 := by simpa only [d348972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42319 p hg
    simpa only [d348972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42321 (p : Pattern) (guard : d348973 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d348972 p = 1 := by simpa only [d348973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42320 p hg
    simpa only [d348973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42322 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42323 (p : Pattern) (guard : d0 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42324 (p : Pattern) (guard : d0 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42325 (p : Pattern) (guard : d0 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42326 (p : Pattern) (guard : d0 p = 1) : d50949 p ≤ (0 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42327 (p : Pattern) (guard : d0 p = 1) : d50951 p ≤ (0 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42328 (p : Pattern) (guard : d0 p = 1) : d50904 p ≤ (0 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42329 (p : Pattern) (guard : d0 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42330 (p : Pattern) (guard : d0 p = 1) : d50906 p ≤ (0 : Int) + d47655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42331 (p : Pattern) (guard : d0 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42332 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare42333 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42334 (p : Pattern) (guard : d15 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42332 p hg
    simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42333 p hg
    simpa only [d15, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42335 (p : Pattern) (guard : d16 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42334 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42336 (p : Pattern) (guard : d17 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42335 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42337 (p : Pattern) (guard : d38813 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42336 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42338 (p : Pattern) (guard : d258091 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42337 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42339 (p : Pattern) (guard : d337158 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42338 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42340 (p : Pattern) (guard : d337173 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42339 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42341 (p : Pattern) (guard : d257183 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42337 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42342 (p : Pattern) (guard : d257184 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42341 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42343 (p : Pattern) (guard : d257185 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42342 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42331 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42344 (p : Pattern) (guard : d348400 p = 1) : d50838 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42340 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42343 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42345 (p : Pattern) (guard : d0 p = 1) : d50839 p ≤ (0 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42346 (p : Pattern) (guard : d348401 p = 1) : d50840 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42344 p hg
    simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42345 p hg
    simpa only [d348401, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42347 (p : Pattern) (guard : d0 p = 1) : d50840 p ≤ (0 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42348 (p : Pattern) (guard : d348402 p = 1) : d50840 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42346 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42347 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42349 (p : Pattern) (guard : d0 p = 1) : d50880 p ≤ (0 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42350 (p : Pattern) (guard : d348403 p = 1) : d50881 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42348 p hg
    simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42349 p hg
    simpa only [d348403, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42351 (p : Pattern) (guard : d0 p = 1) : d50883 p ≤ (0 : Int) + d47662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42352 (p : Pattern) (guard : d348404 p = 1) : d50884 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348403 p = 1 := by simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42350 p hg
    simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42351 p hg
    simpa only [d348404, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42353 (p : Pattern) (guard : d348405 p = 1) : d50907 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42330 p hg
    simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348404 p = 1 := by simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42352 p hg
    simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42354 (p : Pattern) (guard : d0 p = 1) : d50910 p ≤ (0 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42355 (p : Pattern) (guard : d348406 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348405 p = 1 := by simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42353 p hg
    simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42354 p hg
    simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42356 (p : Pattern) (guard : d348407 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348406 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42355 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42357 (p : Pattern) (guard : d348408 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348407 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42356 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42358 (p : Pattern) (guard : d348409 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348406 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42355 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42359 (p : Pattern) (guard : d348410 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348409 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42358 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42360 (p : Pattern) (guard : d348411 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348408 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42357 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348410 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42359 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42361 (p : Pattern) (guard : d348412 p = 1) : d50912 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42328 p hg
    simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348411 p = 1 := by simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42360 p hg
    simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42362 (p : Pattern) (guard : d348413 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348412 p = 1 := by simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42361 p hg
    simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42363 (p : Pattern) (guard : d348414 p = 1) : d50911 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348410 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42359 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42329 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42364 (p : Pattern) (guard : d348415 p = 1) : d50912 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42328 p hg
    simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348414 p = 1 := by simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42363 p hg
    simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42365 (p : Pattern) (guard : d348416 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348415 p = 1 := by simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42364 p hg
    simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42366 (p : Pattern) (guard : d348417 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348413 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42362 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348416 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42365 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42367 (p : Pattern) (guard : d0 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42368 (p : Pattern) (guard : d348418 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348416 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42365 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42369 (p : Pattern) (guard : d348419 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348417 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42366 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348418 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42368 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42370 (p : Pattern) (guard : d348420 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348419 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42369 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42371 (p : Pattern) (guard : d0 p = 1) : d50931 p ≤ (0 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42372 (p : Pattern) (guard : d348421 p = 1) : d50953 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348420 p = 1 := by simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42370 p hg
    simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42373 (p : Pattern) (guard : d348422 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348421 p = 1 := by simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42372 p hg
    simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42374 (p : Pattern) (guard : d348423 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348418 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42368 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42375 (p : Pattern) (guard : d348424 p = 1) : d50952 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348423 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42374 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42367 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42376 (p : Pattern) (guard : d348425 p = 1) : d50953 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348424 p = 1 := by simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42375 p hg
    simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42377 (p : Pattern) (guard : d348426 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348425 p = 1 := by simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42376 p hg
    simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42378 (p : Pattern) (guard : d348427 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42373 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348426 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42377 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42379 (p : Pattern) (guard : d348428 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348427 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42378 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42380 (p : Pattern) (guard : d348429 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348428 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42379 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42381 (p : Pattern) (guard : d348430 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348429 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42380 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42382 (p : Pattern) (guard : d348431 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348426 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42377 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42383 (p : Pattern) (guard : d348432 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348431 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42382 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42384 (p : Pattern) (guard : d348433 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348432 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42383 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42385 (p : Pattern) (guard : d348434 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348433 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42384 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42386 (p : Pattern) (guard : d348435 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348430 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42381 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348434 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42387 (p : Pattern) (guard : d348436 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348435 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42386 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42388 (p : Pattern) (guard : d348437 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348436 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42387 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42389 (p : Pattern) (guard : d348438 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348437 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42388 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42390 (p : Pattern) (guard : d348439 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348438 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42389 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42391 (p : Pattern) (guard : d348440 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348439 p = 1 := by simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42390 p hg
    simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42392 (p : Pattern) (guard : d0 p = 1) : d50923 p ≤ (0 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42393 (p : Pattern) (guard : d0 p = 1) : d50929 p ≤ (0 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42394 (p : Pattern) (guard : d348413 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42393 p hg
    simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348412 p = 1 := by simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42361 p hg
    simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42395 (p : Pattern) (guard : d348416 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42393 p hg
    simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348415 p = 1 := by simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42364 p hg
    simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42396 (p : Pattern) (guard : d348417 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348413 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42394 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348416 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42395 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42397 (p : Pattern) (guard : d0 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42398 (p : Pattern) (guard : d348418 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348416 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42395 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42399 (p : Pattern) (guard : d348419 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348417 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348418 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42400 (p : Pattern) (guard : d348420 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348419 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42399 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42401 (p : Pattern) (guard : d348421 p = 1) : d50932 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348420 p = 1 := by simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42400 p hg
    simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42402 (p : Pattern) (guard : d348422 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42392 p hg
    simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348421 p = 1 := by simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42401 p hg
    simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42403 (p : Pattern) (guard : d348423 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348418 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42404 (p : Pattern) (guard : d348424 p = 1) : d50930 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348423 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42403 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42397 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42405 (p : Pattern) (guard : d348425 p = 1) : d50932 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348424 p = 1 := by simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42404 p hg
    simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42371 p hg
    simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42406 (p : Pattern) (guard : d348426 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42392 p hg
    simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348425 p = 1 := by simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42405 p hg
    simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42407 (p : Pattern) (guard : d348427 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42402 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348426 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42406 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42408 (p : Pattern) (guard : d348428 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348427 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42407 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42409 (p : Pattern) (guard : d348429 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348428 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42408 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42410 (p : Pattern) (guard : d348430 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348429 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42409 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42411 (p : Pattern) (guard : d348431 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348426 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42406 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42412 (p : Pattern) (guard : d348432 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348431 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42411 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42413 (p : Pattern) (guard : d348433 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348432 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42412 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42414 (p : Pattern) (guard : d348434 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348433 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42413 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42415 (p : Pattern) (guard : d348435 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348430 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42410 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348434 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42414 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42416 (p : Pattern) (guard : d348436 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348435 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42415 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42417 (p : Pattern) (guard : d348437 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348436 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42416 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42418 (p : Pattern) (guard : d348438 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348437 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42417 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42419 (p : Pattern) (guard : d348439 p = 1) : d50933 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348438 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42418 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42420 (p : Pattern) (guard : d348443 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348429 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42380 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42421 (p : Pattern) (guard : d348444 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348433 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42384 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42422 (p : Pattern) (guard : d348445 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348443 p = 1 := by simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42420 p hg
    simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348444 p = 1 := by simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42421 p hg
    simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42423 (p : Pattern) (guard : d348446 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348445 p = 1 := by simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42422 p hg
    simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42424 (p : Pattern) (guard : d348447 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348446 p = 1 := by simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42423 p hg
    simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42425 (p : Pattern) (guard : d348448 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348447 p = 1 := by simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42424 p hg
    simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42426 (p : Pattern) (guard : d348449 p = 1) : d50954 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42325 p hg
    simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348448 p = 1 := by simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42425 p hg
    simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42427 (p : Pattern) (guard : d348450 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348439 p = 1 := by simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42419 p hg
    simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348449 p = 1 := by simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42426 p hg
    simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42428 (p : Pattern) (guard : d348451 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348440 p = 1 := by simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42391 p hg
    simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348450 p = 1 := by simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42427 p hg
    simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42429 (p : Pattern) (guard : d348452 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348451 p = 1 := by simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42428 p hg
    simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42323 p hg
    simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42430 (p : Pattern) (guard : d349135 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348452 p = 1 := by simpa only [d349135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42429 p hg
    simpa only [d349135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42323 p hg
    simpa only [d349135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42431 (p : Pattern) (guard : d349136 p = 1) : d50955 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42323 p hg
    simpa only [d349136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349135 p = 1 := by simpa only [d349136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42430 p hg
    simpa only [d349136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42432 (p : Pattern) (guard : d0 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42433 (p : Pattern) (guard : d0 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42434 (p : Pattern) (guard : d0 p = 1) : d51030 p ≤ (0 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42435 (p : Pattern) (guard : d0 p = 1) : d51033 p ≤ (0 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42436 (p : Pattern) (guard : d0 p = 1) : d51015 p ≤ (0 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42437 (p : Pattern) (guard : d0 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42438 (p : Pattern) (guard : d0 p = 1) : d51017 p ≤ (0 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42439 (p : Pattern) (guard : d0 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42440 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare42441 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42442 (p : Pattern) (guard : d15 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42440 p hg
    simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42441 p hg
    simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42443 (p : Pattern) (guard : d16 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42442 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42444 (p : Pattern) (guard : d17 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42443 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42445 (p : Pattern) (guard : d38813 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42444 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42446 (p : Pattern) (guard : d258091 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42445 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42447 (p : Pattern) (guard : d337158 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42446 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42448 (p : Pattern) (guard : d337173 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42447 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42449 (p : Pattern) (guard : d257183 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42445 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42450 (p : Pattern) (guard : d257184 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42449 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42451 (p : Pattern) (guard : d257185 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42439 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42452 (p : Pattern) (guard : d348400 p = 1) : d50965 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42448 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42451 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42453 (p : Pattern) (guard : d0 p = 1) : d50966 p ≤ (0 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42454 (p : Pattern) (guard : d348401 p = 1) : d50967 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42452 p hg
    simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42453 p hg
    simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42455 (p : Pattern) (guard : d0 p = 1) : d50967 p ≤ (0 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42456 (p : Pattern) (guard : d348402 p = 1) : d50967 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42455 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42457 (p : Pattern) (guard : d0 p = 1) : d50882 p ≤ (0 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42458 (p : Pattern) (guard : d348403 p = 1) : d50997 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42456 p hg
    simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42459 (p : Pattern) (guard : d348404 p = 1) : d50998 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348403 p = 1 := by simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42458 p hg
    simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42460 (p : Pattern) (guard : d348405 p = 1) : d51018 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42438 p hg
    simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348404 p = 1 := by simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42459 p hg
    simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42461 (p : Pattern) (guard : d0 p = 1) : d51021 p ≤ (0 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42462 (p : Pattern) (guard : d348406 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348405 p = 1 := by simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42460 p hg
    simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42461 p hg
    simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42463 (p : Pattern) (guard : d348407 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348406 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42462 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42464 (p : Pattern) (guard : d348408 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348407 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42463 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42465 (p : Pattern) (guard : d348409 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348406 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42462 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42466 (p : Pattern) (guard : d348410 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348409 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42465 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42467 (p : Pattern) (guard : d348411 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348408 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42464 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348410 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42466 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42468 (p : Pattern) (guard : d348412 p = 1) : d51023 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42436 p hg
    simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348411 p = 1 := by simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42467 p hg
    simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42469 (p : Pattern) (guard : d348413 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42435 p hg
    simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348412 p = 1 := by simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42468 p hg
    simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42470 (p : Pattern) (guard : d348414 p = 1) : d51022 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348410 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42466 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42437 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42471 (p : Pattern) (guard : d348415 p = 1) : d51023 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42436 p hg
    simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348414 p = 1 := by simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42470 p hg
    simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42472 (p : Pattern) (guard : d348416 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42435 p hg
    simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348415 p = 1 := by simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42471 p hg
    simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42473 (p : Pattern) (guard : d348417 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348413 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42469 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348416 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42472 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42474 (p : Pattern) (guard : d0 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42475 (p : Pattern) (guard : d348418 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348416 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42472 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42476 (p : Pattern) (guard : d348419 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348417 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42473 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348418 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42475 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42477 (p : Pattern) (guard : d348420 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348419 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42476 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42478 (p : Pattern) (guard : d0 p = 1) : d51035 p ≤ (0 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42479 (p : Pattern) (guard : d348421 p = 1) : d51036 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348420 p = 1 := by simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42477 p hg
    simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42480 (p : Pattern) (guard : d348422 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42434 p hg
    simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348421 p = 1 := by simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42479 p hg
    simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42481 (p : Pattern) (guard : d348423 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348418 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42475 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42482 (p : Pattern) (guard : d348424 p = 1) : d51034 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348423 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42481 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42474 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42483 (p : Pattern) (guard : d348425 p = 1) : d51036 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348424 p = 1 := by simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42482 p hg
    simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42478 p hg
    simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42484 (p : Pattern) (guard : d348426 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42434 p hg
    simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348425 p = 1 := by simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42483 p hg
    simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42485 (p : Pattern) (guard : d348427 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42480 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348426 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42484 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42486 (p : Pattern) (guard : d348428 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348427 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42485 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42487 (p : Pattern) (guard : d348429 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348428 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42486 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42488 (p : Pattern) (guard : d348443 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348429 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42487 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42489 (p : Pattern) (guard : d348431 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348426 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42484 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42490 (p : Pattern) (guard : d348432 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348431 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42489 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42491 (p : Pattern) (guard : d348433 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348432 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42490 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42492 (p : Pattern) (guard : d348444 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348433 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42491 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42493 (p : Pattern) (guard : d348445 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348443 p = 1 := by simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42488 p hg
    simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348444 p = 1 := by simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42492 p hg
    simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42494 (p : Pattern) (guard : d348446 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348445 p = 1 := by simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42493 p hg
    simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42495 (p : Pattern) (guard : d348447 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348446 p = 1 := by simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42494 p hg
    simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42496 (p : Pattern) (guard : d348448 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348447 p = 1 := by simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42495 p hg
    simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42497 (p : Pattern) (guard : d348449 p = 1) : d51037 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42433 p hg
    simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348448 p = 1 := by simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42496 p hg
    simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42498 (p : Pattern) (guard : d349137 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349137, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d349137, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348449 p = 1 := by simpa only [d349137, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42497 p hg
    simpa only [d349137, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42499 (p : Pattern) (guard : d349138 p = 1) : d51038 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42432 p hg
    simpa only [d349138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349137 p = 1 := by simpa only [d349138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42498 p hg
    simpa only [d349138, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
