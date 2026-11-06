import NetHack.Soko22Hazard87.Compare156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39250 (p : Pattern) (guard : d317932 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317931 p = 1 := by simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39249 p hg
    simpa only [d317932, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39251 (p : Pattern) (guard : d317933 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317924 p = 1 := by simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39246 p hg
    simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317932 p = 1 := by simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39250 p hg
    simpa only [d317933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39252 (p : Pattern) (guard : d317934 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317933 p = 1 := by simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39251 p hg
    simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39253 (p : Pattern) (guard : d317935 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317934 p = 1 := by simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39252 p hg
    simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39254 (p : Pattern) (guard : d317936 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317935 p = 1 := by simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39253 p hg
    simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39255 (p : Pattern) (guard : d317950 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317932 p = 1 := by simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39250 p hg
    simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39256 (p : Pattern) (guard : d317951 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317950 p = 1 := by simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39255 p hg
    simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39257 (p : Pattern) (guard : d317952 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317951 p = 1 := by simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39256 p hg
    simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39258 (p : Pattern) (guard : d317953 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317952 p = 1 := by simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39257 p hg
    simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39259 (p : Pattern) (guard : d318453 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317936 p = 1 := by simpa only [d318453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39254 p hg
    simpa only [d318453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317953 p = 1 := by simpa only [d318453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39258 p hg
    simpa only [d318453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39260 (p : Pattern) (guard : d318454 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318453 p = 1 := by simpa only [d318454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39259 p hg
    simpa only [d318454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39261 (p : Pattern) (guard : d318455 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318454 p = 1 := by simpa only [d318455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39260 p hg
    simpa only [d318455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39262 (p : Pattern) (guard : d318456 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318455 p = 1 := by simpa only [d318456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d318456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39263 (p : Pattern) (guard : d318457 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318456 p = 1 := by simpa only [d318457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39262 p hg
    simpa only [d318457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39264 (p : Pattern) (guard : d318458 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318458, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318458, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318457 p = 1 := by simpa only [d318458, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39263 p hg
    simpa only [d318458, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39265 (p : Pattern) (guard : d318459 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318458 p = 1 := by simpa only [d318459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39264 p hg
    simpa only [d318459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39266 (p : Pattern) (guard : d318460 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318459 p = 1 := by simpa only [d318460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39265 p hg
    simpa only [d318460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39267 (p : Pattern) (guard : d318461 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318460 p = 1 := by simpa only [d318461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39266 p hg
    simpa only [d318461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39268 (p : Pattern) (guard : d318462 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318461 p = 1 := by simpa only [d318462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39267 p hg
    simpa only [d318462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39269 (p : Pattern) (guard : d318463 p = 1) : d50492 p ≤ (2 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318462 p = 1 := by simpa only [d318463, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39268 p hg
    simpa only [d318463, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318463, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38023 p hg
    simpa only [d318463, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39270 (p : Pattern) (guard : d318464 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d318452 p = 1 := by simpa only [d318464, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39102 p hg
    simpa only [d318464, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318463 p = 1 := by simpa only [d318464, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39269 p hg
    simpa only [d318464, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39271 (p : Pattern) (guard : d318465 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318464 p = 1 := by simpa only [d318465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39270 p hg
    simpa only [d318465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39272 (p : Pattern) (guard : d318466 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318465 p = 1 := by simpa only [d318466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39271 p hg
    simpa only [d318466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39273 (p : Pattern) (guard : d318467 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318466 p = 1 := by simpa only [d318467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39272 p hg
    simpa only [d318467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39274 (p : Pattern) (guard : d318468 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318467 p = 1 := by simpa only [d318468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39273 p hg
    simpa only [d318468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39275 (p : Pattern) (guard : d318469 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318468 p = 1 := by simpa only [d318469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39274 p hg
    simpa only [d318469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39276 (p : Pattern) (guard : d318470 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318469 p = 1 := by simpa only [d318470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39275 p hg
    simpa only [d318470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39277 (p : Pattern) (guard : d318471 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318470 p = 1 := by simpa only [d318471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39276 p hg
    simpa only [d318471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39278 (p : Pattern) (guard : d318472 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318471 p = 1 := by simpa only [d318472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39277 p hg
    simpa only [d318472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39279 (p : Pattern) (guard : d318473 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318472 p = 1 := by simpa only [d318473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39278 p hg
    simpa only [d318473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39280 (p : Pattern) (guard : d318474 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d318444 p = 1 := by simpa only [d318474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38854 p hg
    simpa only [d318474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318473 p = 1 := by simpa only [d318474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39279 p hg
    simpa only [d318474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39281 (p : Pattern) (guard : d2013 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare39282 (p : Pattern) (guard : d2027 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39281 p hg
    simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d2027, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39283 (p : Pattern) (guard : d2028 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39282 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39284 (p : Pattern) (guard : d2029 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39283 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39285 (p : Pattern) (guard : d2030 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39284 p hg
    simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d2030, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39286 (p : Pattern) (guard : d2031 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39285 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39287 (p : Pattern) (guard : d317063 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39286 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39288 (p : Pattern) (guard : d317064 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39287 p hg
    simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d317064, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39289 (p : Pattern) (guard : d317065 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39288 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39290 (p : Pattern) (guard : d317066 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39289 p hg
    simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317066, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39291 (p : Pattern) (guard : d317067 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317066 p = 1 := by simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39290 p hg
    simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317067, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39292 (p : Pattern) (guard : d317068 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317067 p = 1 := by simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39291 p hg
    simpa only [d317068, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39293 (p : Pattern) (guard : d317069 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317068 p = 1 := by simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39292 p hg
    simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317069, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39294 (p : Pattern) (guard : d317070 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39288 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39295 (p : Pattern) (guard : d317071 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39294 p hg
    simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317071, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39296 (p : Pattern) (guard : d317072 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317071 p = 1 := by simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39295 p hg
    simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317072, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39297 (p : Pattern) (guard : d317073 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317072 p = 1 := by simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39296 p hg
    simpa only [d317073, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39298 (p : Pattern) (guard : d317074 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317073 p = 1 := by simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39297 p hg
    simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317074, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39299 (p : Pattern) (guard : d317075 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317069 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39293 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317074 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39298 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39300 (p : Pattern) (guard : d317076 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317075 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39299 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39301 (p : Pattern) (guard : d27032 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39285 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39302 (p : Pattern) (guard : d235783 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39301 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39303 (p : Pattern) (guard : d235784 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39302 p hg
    simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d235784, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39304 (p : Pattern) (guard : d317976 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39288 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39303 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39305 (p : Pattern) (guard : d317977 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39304 p hg
    simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317977, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39306 (p : Pattern) (guard : d317978 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317977 p = 1 := by simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39305 p hg
    simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317978, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39307 (p : Pattern) (guard : d317979 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317978 p = 1 := by simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39306 p hg
    simpa only [d317979, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39308 (p : Pattern) (guard : d317980 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317979 p = 1 := by simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39307 p hg
    simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317980, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39309 (p : Pattern) (guard : d317094 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39303 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39310 (p : Pattern) (guard : d317095 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39309 p hg
    simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317095, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39311 (p : Pattern) (guard : d317096 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317095 p = 1 := by simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39310 p hg
    simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317096, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39312 (p : Pattern) (guard : d317097 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317096 p = 1 := by simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39311 p hg
    simpa only [d317097, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39313 (p : Pattern) (guard : d317098 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317097 p = 1 := by simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39312 p hg
    simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317098, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39314 (p : Pattern) (guard : d317981 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317980 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39308 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317098 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39313 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39315 (p : Pattern) (guard : d317982 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317981 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39314 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39316 (p : Pattern) (guard : d317983 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317076 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39300 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317982 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39315 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39317 (p : Pattern) (guard : d317984 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317983 p = 1 := by simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39316 p hg
    simpa only [d317984, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39318 (p : Pattern) (guard : d317985 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317984 p = 1 := by simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39317 p hg
    simpa only [d317985, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39319 (p : Pattern) (guard : d317099 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317098 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39313 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39320 (p : Pattern) (guard : d317100 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317099 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39319 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39321 (p : Pattern) (guard : d317986 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317982 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39315 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317100 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39320 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39322 (p : Pattern) (guard : d317987 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317986 p = 1 := by simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d317987, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39323 (p : Pattern) (guard : d317988 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317987 p = 1 := by simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39322 p hg
    simpa only [d317988, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39324 (p : Pattern) (guard : d317989 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317985 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39318 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317988 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39323 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39325 (p : Pattern) (guard : d317990 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317988 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39323 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39326 (p : Pattern) (guard : d317991 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317989 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39324 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317990 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39325 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39327 (p : Pattern) (guard : d317992 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317991 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39326 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39328 (p : Pattern) (guard : d317993 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317992 p = 1 := by simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39327 p hg
    simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317993, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39329 (p : Pattern) (guard : d317994 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317993 p = 1 := by simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39328 p hg
    simpa only [d317994, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39330 (p : Pattern) (guard : d317995 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317990 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39325 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39331 (p : Pattern) (guard : d317996 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317995 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39330 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39332 (p : Pattern) (guard : d317997 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317996 p = 1 := by simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39331 p hg
    simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317997, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39333 (p : Pattern) (guard : d317998 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317997 p = 1 := by simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39332 p hg
    simpa only [d317998, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39334 (p : Pattern) (guard : d317999 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39329 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317998 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39333 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39335 (p : Pattern) (guard : d318000 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317999 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39334 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39336 (p : Pattern) (guard : d318001 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318000 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39335 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39337 (p : Pattern) (guard : d318002 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318001 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39336 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39338 (p : Pattern) (guard : d318003 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317998 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39333 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39339 (p : Pattern) (guard : d318004 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318003 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39338 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39340 (p : Pattern) (guard : d318005 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318004 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39339 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39341 (p : Pattern) (guard : d318006 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318005 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39340 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39342 (p : Pattern) (guard : d318007 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318002 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39337 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318006 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39341 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39343 (p : Pattern) (guard : d318008 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318007 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39342 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39344 (p : Pattern) (guard : d318009 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318008 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39343 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39345 (p : Pattern) (guard : d318010 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318009 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39344 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39346 (p : Pattern) (guard : d318011 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318010 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39345 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39347 (p : Pattern) (guard : d318012 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318011 p = 1 := by simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39346 p hg
    simpa only [d318012, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39348 (p : Pattern) (guard : d317985 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317984 p = 1 := by simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39317 p hg
    simpa only [d317985, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39349 (p : Pattern) (guard : d317988 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317987 p = 1 := by simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39322 p hg
    simpa only [d317988, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39350 (p : Pattern) (guard : d317989 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317985 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39348 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317988 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39349 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39351 (p : Pattern) (guard : d317990 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317988 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39349 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39352 (p : Pattern) (guard : d317991 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317989 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39350 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317990 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39351 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39353 (p : Pattern) (guard : d317992 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317991 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39352 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39354 (p : Pattern) (guard : d317993 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317992 p = 1 := by simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39353 p hg
    simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317993, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39355 (p : Pattern) (guard : d317994 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317993 p = 1 := by simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39354 p hg
    simpa only [d317994, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39356 (p : Pattern) (guard : d317995 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317990 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39351 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39357 (p : Pattern) (guard : d317996 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317995 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39356 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39358 (p : Pattern) (guard : d317997 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317996 p = 1 := by simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39357 p hg
    simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317997, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39359 (p : Pattern) (guard : d317998 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317997 p = 1 := by simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39358 p hg
    simpa only [d317998, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39360 (p : Pattern) (guard : d317999 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39355 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317998 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39359 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39361 (p : Pattern) (guard : d318000 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317999 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39360 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39362 (p : Pattern) (guard : d318001 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318000 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39361 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39363 (p : Pattern) (guard : d318002 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318001 p = 1 := by simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39362 p hg
    simpa only [d318002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39364 (p : Pattern) (guard : d318003 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317998 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39359 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39365 (p : Pattern) (guard : d318004 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318003 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39364 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39366 (p : Pattern) (guard : d318005 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318004 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39367 (p : Pattern) (guard : d318006 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318005 p = 1 := by simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39366 p hg
    simpa only [d318006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39368 (p : Pattern) (guard : d318007 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318002 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39363 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318006 p = 1 := by simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39367 p hg
    simpa only [d318007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39369 (p : Pattern) (guard : d318008 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318007 p = 1 := by simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39368 p hg
    simpa only [d318008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39370 (p : Pattern) (guard : d318009 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318008 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39369 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39371 (p : Pattern) (guard : d318010 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318009 p = 1 := by simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39370 p hg
    simpa only [d318010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39372 (p : Pattern) (guard : d318011 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318010 p = 1 := by simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39371 p hg
    simpa only [d318011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39373 (p : Pattern) (guard : d318015 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318001 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39336 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39374 (p : Pattern) (guard : d318016 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318005 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39340 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39375 (p : Pattern) (guard : d318017 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318015 p = 1 := by simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39373 p hg
    simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318016 p = 1 := by simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39374 p hg
    simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39376 (p : Pattern) (guard : d318018 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318017 p = 1 := by simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39375 p hg
    simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39377 (p : Pattern) (guard : d318019 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318018 p = 1 := by simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39376 p hg
    simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39378 (p : Pattern) (guard : d318020 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318019 p = 1 := by simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39377 p hg
    simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39379 (p : Pattern) (guard : d318021 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318020 p = 1 := by simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39378 p hg
    simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39380 (p : Pattern) (guard : d318022 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d318011 p = 1 := by simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39372 p hg
    simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318021 p = 1 := by simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39379 p hg
    simpa only [d318022, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39381 (p : Pattern) (guard : d318023 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d318012 p = 1 := by simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39347 p hg
    simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318022 p = 1 := by simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39380 p hg
    simpa only [d318023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39382 (p : Pattern) (guard : d318024 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318023 p = 1 := by simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39381 p hg
    simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39383 (p : Pattern) (guard : d318475 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318024 p = 1 := by simpa only [d318475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39382 p hg
    simpa only [d318475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39384 (p : Pattern) (guard : d318476 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318475 p = 1 := by simpa only [d318476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39383 p hg
    simpa only [d318476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39385 (p : Pattern) (guard : d2013 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare39386 (p : Pattern) (guard : d2027 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39385 p hg
    simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d2027, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39387 (p : Pattern) (guard : d2028 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39386 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39388 (p : Pattern) (guard : d2029 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39387 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39389 (p : Pattern) (guard : d2030 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39388 p hg
    simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d2030, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39390 (p : Pattern) (guard : d2031 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39389 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39391 (p : Pattern) (guard : d317063 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39390 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39392 (p : Pattern) (guard : d317064 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39391 p hg
    simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d317064, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39393 (p : Pattern) (guard : d317065 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39392 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39394 (p : Pattern) (guard : d317066 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39393 p hg
    simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317066, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39395 (p : Pattern) (guard : d317067 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317066 p = 1 := by simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39394 p hg
    simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317067, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39396 (p : Pattern) (guard : d317068 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317067 p = 1 := by simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39395 p hg
    simpa only [d317068, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39397 (p : Pattern) (guard : d317069 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317068 p = 1 := by simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39396 p hg
    simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317069, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39398 (p : Pattern) (guard : d317070 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39392 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39399 (p : Pattern) (guard : d317071 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39398 p hg
    simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317071, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39400 (p : Pattern) (guard : d317072 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317071 p = 1 := by simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39399 p hg
    simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317072, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39401 (p : Pattern) (guard : d317073 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317072 p = 1 := by simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39400 p hg
    simpa only [d317073, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39402 (p : Pattern) (guard : d317074 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317073 p = 1 := by simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39401 p hg
    simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317074, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39403 (p : Pattern) (guard : d317075 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317069 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39397 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317074 p = 1 := by simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39402 p hg
    simpa only [d317075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39404 (p : Pattern) (guard : d317076 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317075 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39403 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39405 (p : Pattern) (guard : d27032 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39389 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39406 (p : Pattern) (guard : d235783 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39405 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39407 (p : Pattern) (guard : d235784 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39406 p hg
    simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d235784, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39408 (p : Pattern) (guard : d317976 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39392 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39407 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39409 (p : Pattern) (guard : d317977 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39408 p hg
    simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317977, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39410 (p : Pattern) (guard : d317978 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317977 p = 1 := by simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39409 p hg
    simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317978, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39411 (p : Pattern) (guard : d317979 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317978 p = 1 := by simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39410 p hg
    simpa only [d317979, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39412 (p : Pattern) (guard : d317980 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317979 p = 1 := by simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39411 p hg
    simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317980, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39413 (p : Pattern) (guard : d317094 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39407 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39414 (p : Pattern) (guard : d317095 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39413 p hg
    simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317095, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39415 (p : Pattern) (guard : d317096 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317095 p = 1 := by simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39414 p hg
    simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317096, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39416 (p : Pattern) (guard : d317097 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317096 p = 1 := by simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39415 p hg
    simpa only [d317097, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39417 (p : Pattern) (guard : d317098 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317097 p = 1 := by simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39416 p hg
    simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317098, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39418 (p : Pattern) (guard : d317981 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317980 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39412 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317098 p = 1 := by simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39417 p hg
    simpa only [d317981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39419 (p : Pattern) (guard : d317982 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317981 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39418 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39420 (p : Pattern) (guard : d317983 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317076 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39404 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317982 p = 1 := by simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39419 p hg
    simpa only [d317983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39421 (p : Pattern) (guard : d317984 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317983 p = 1 := by simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39420 p hg
    simpa only [d317984, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39422 (p : Pattern) (guard : d317985 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317984 p = 1 := by simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39421 p hg
    simpa only [d317985, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39423 (p : Pattern) (guard : d317099 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317098 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39417 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39424 (p : Pattern) (guard : d317100 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317099 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39423 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39425 (p : Pattern) (guard : d317986 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317982 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39419 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317100 p = 1 := by simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39424 p hg
    simpa only [d317986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39426 (p : Pattern) (guard : d317987 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317986 p = 1 := by simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39425 p hg
    simpa only [d317987, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39427 (p : Pattern) (guard : d317988 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317987 p = 1 := by simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39426 p hg
    simpa only [d317988, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39428 (p : Pattern) (guard : d317989 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317985 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39422 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317988 p = 1 := by simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39427 p hg
    simpa only [d317989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39429 (p : Pattern) (guard : d317990 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317988 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39427 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39430 (p : Pattern) (guard : d317991 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317989 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39428 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317990 p = 1 := by simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39429 p hg
    simpa only [d317991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39431 (p : Pattern) (guard : d317992 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317991 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39430 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39432 (p : Pattern) (guard : d317993 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317992 p = 1 := by simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39431 p hg
    simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d317993, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39433 (p : Pattern) (guard : d317994 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317993 p = 1 := by simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39432 p hg
    simpa only [d317994, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39434 (p : Pattern) (guard : d317995 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317990 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39429 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39435 (p : Pattern) (guard : d317996 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317995 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39434 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39436 (p : Pattern) (guard : d317997 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317996 p = 1 := by simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39435 p hg
    simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d317997, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39437 (p : Pattern) (guard : d317998 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317997 p = 1 := by simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39436 p hg
    simpa only [d317998, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39438 (p : Pattern) (guard : d317999 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317994 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39433 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317998 p = 1 := by simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39437 p hg
    simpa only [d317999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39439 (p : Pattern) (guard : d318000 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317999 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39438 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39440 (p : Pattern) (guard : d318001 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318000 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39439 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39441 (p : Pattern) (guard : d318015 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318001 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39440 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39442 (p : Pattern) (guard : d318003 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317998 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39437 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39443 (p : Pattern) (guard : d318004 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318003 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39442 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39444 (p : Pattern) (guard : d318005 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318004 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39443 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39445 (p : Pattern) (guard : d318016 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318005 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39444 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39446 (p : Pattern) (guard : d318017 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318015 p = 1 := by simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39441 p hg
    simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318016 p = 1 := by simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39445 p hg
    simpa only [d318017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39447 (p : Pattern) (guard : d318018 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318017 p = 1 := by simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39446 p hg
    simpa only [d318018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39448 (p : Pattern) (guard : d318019 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318018 p = 1 := by simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39447 p hg
    simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39449 (p : Pattern) (guard : d318020 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318019 p = 1 := by simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39448 p hg
    simpa only [d318020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39450 (p : Pattern) (guard : d318021 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318020 p = 1 := by simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39449 p hg
    simpa only [d318021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39451 (p : Pattern) (guard : d318477 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318477, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318477, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318021 p = 1 := by simpa only [d318477, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39450 p hg
    simpa only [d318477, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39452 (p : Pattern) (guard : d318478 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318477 p = 1 := by simpa only [d318478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39451 p hg
    simpa only [d318478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39453 (p : Pattern) (guard : d318479 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318478 p = 1 := by simpa only [d318479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39452 p hg
    simpa only [d318479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39454 (p : Pattern) (guard : d318480 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318479 p = 1 := by simpa only [d318480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39453 p hg
    simpa only [d318480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39455 (p : Pattern) (guard : d318481 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318480 p = 1 := by simpa only [d318481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39454 p hg
    simpa only [d318481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39456 (p : Pattern) (guard : d318482 p = 1) : d50390 p ≤ (2 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318476 p = 1 := by simpa only [d318482, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39384 p hg
    simpa only [d318482, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318481 p = 1 := by simpa only [d318482, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39455 p hg
    simpa only [d318482, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39457 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare39458 (p : Pattern) (guard : d2027 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39457 p hg
    simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d2027, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39459 (p : Pattern) (guard : d2028 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39458 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39460 (p : Pattern) (guard : d2029 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39459 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39461 (p : Pattern) (guard : d2030 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39460 p hg
    simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d2030, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39462 (p : Pattern) (guard : d2031 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39461 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39463 (p : Pattern) (guard : d317063 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39462 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39464 (p : Pattern) (guard : d317064 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39463 p hg
    simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d317064, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39465 (p : Pattern) (guard : d317065 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39464 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39466 (p : Pattern) (guard : d317253 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317065 p = 1 := by simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39465 p hg
    simpa only [d317253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39467 (p : Pattern) (guard : d317066 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39289 p hg
    simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317066, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39468 (p : Pattern) (guard : d317254 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317253 p = 1 := by simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39466 p hg
    simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317066 p = 1 := by simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39467 p hg
    simpa only [d317254, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39469 (p : Pattern) (guard : d2013 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare39470 (p : Pattern) (guard : d2027 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39469 p hg
    simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d2027, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39471 (p : Pattern) (guard : d2028 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39470 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39472 (p : Pattern) (guard : d2029 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39471 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39473 (p : Pattern) (guard : d2030 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39472 p hg
    simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d2030, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39474 (p : Pattern) (guard : d2031 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39473 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39475 (p : Pattern) (guard : d317063 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39474 p hg
    simpa only [d317063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39476 (p : Pattern) (guard : d317064 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317063 p = 1 := by simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39475 p hg
    simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d317064, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39477 (p : Pattern) (guard : d317065 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317064 p = 1 := by simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39476 p hg
    simpa only [d317065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39478 (p : Pattern) (guard : d317066 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317065 p = 1 := by simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39477 p hg
    simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317066, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39479 (p : Pattern) (guard : d317067 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317066 p = 1 := by simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39478 p hg
    simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317067, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39480 (p : Pattern) (guard : d317255 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317254 p = 1 := by simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39468 p hg
    simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317067 p = 1 := by simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39479 p hg
    simpa only [d317255, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39481 (p : Pattern) (guard : d317256 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317255 p = 1 := by simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39480 p hg
    simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317256, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39482 (p : Pattern) (guard : d317070 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39464 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39483 (p : Pattern) (guard : d317257 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317070 p = 1 := by simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39482 p hg
    simpa only [d317257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39484 (p : Pattern) (guard : d317071 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39294 p hg
    simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317071, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39485 (p : Pattern) (guard : d317258 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317257 p = 1 := by simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39483 p hg
    simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317071 p = 1 := by simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39484 p hg
    simpa only [d317258, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39486 (p : Pattern) (guard : d317070 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39476 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d317070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39487 (p : Pattern) (guard : d317071 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317070 p = 1 := by simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39486 p hg
    simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317071, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39488 (p : Pattern) (guard : d317072 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317071 p = 1 := by simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39487 p hg
    simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317072, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39489 (p : Pattern) (guard : d317259 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317258 p = 1 := by simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39485 p hg
    simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317072 p = 1 := by simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39488 p hg
    simpa only [d317259, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39490 (p : Pattern) (guard : d317260 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317259 p = 1 := by simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39489 p hg
    simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317260, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39491 (p : Pattern) (guard : d317261 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317256 p = 1 := by simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39481 p hg
    simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317260 p = 1 := by simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39490 p hg
    simpa only [d317261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39492 (p : Pattern) (guard : d317262 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317261 p = 1 := by simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39491 p hg
    simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39493 (p : Pattern) (guard : d27032 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39461 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39494 (p : Pattern) (guard : d235783 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39493 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39495 (p : Pattern) (guard : d235784 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39494 p hg
    simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d235784, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39496 (p : Pattern) (guard : d317976 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39464 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39495 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39497 (p : Pattern) (guard : d318111 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317976 p = 1 := by simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39496 p hg
    simpa only [d318111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39498 (p : Pattern) (guard : d317977 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39304 p hg
    simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317977, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39499 (p : Pattern) (guard : d318112 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d318111 p = 1 := by simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39497 p hg
    simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317977 p = 1 := by simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39498 p hg
    simpa only [d318112, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
