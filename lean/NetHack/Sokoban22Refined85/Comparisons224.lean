/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons223
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31360 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31361 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (9 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31359 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31360 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31362 (p : Pattern) (guard : d6326 p = 1) : d190 p ≤ (9 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31358 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31361 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31363 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d8 p := by
  change (12 : Int) ≤ (9 : Int) + 8
  decide
theorem compare31364 (p : Pattern) (guard : d6326 p = 1) : d315 p ≤ (9 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31358 p hg
    simpa only [d6326, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31363 p hg
    simpa only [d6326, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31365 (p : Pattern) (guard : d6326 p = 1) : d3916 p ≤ (9 : Int) + d8 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31362 p hg
    simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31364 p hg
    simpa only [d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31366 (p : Pattern) (guard : d6326 p = 1) : d3917 p ≤ (9 : Int) + d8 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31365 p hg
    simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31364 p hg
    simpa only [d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31367 (p : Pattern) (guard : d6326 p = 1) : d3918 p ≤ (9 : Int) + d8 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31362 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31366 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31368 (p : Pattern) (guard : d6326 p = 1) : d3919 p ≤ (9 : Int) + d6482 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3919, d6482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31366 p hg
    simpa only [d3919, d6482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3919, d6482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3919, d6482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31369 (p : Pattern) (guard : d6326 p = 1) : d3920 p ≤ (9 : Int) + d6483 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3920, d6483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31367 p hg
    simpa only [d3920, d6483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3920, d6483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31368 p hg
    simpa only [d3920, d6483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31370 (p : Pattern) (guard : d6326 p = 1) : d3921 p ≤ (9 : Int) + d6484 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3921, d6484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31059 p hg
    simpa only [d3921, d6484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3921, d6484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31369 p hg
    simpa only [d3921, d6484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31371 (p : Pattern) (guard : d6326 p = 1) : d3922 p ≤ (9 : Int) + d6485 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3922, d6485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31370 p hg
    simpa only [d3922, d6485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3922, d6485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3922, d6485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31372 (p : Pattern) (guard : d6326 p = 1) : d3923 p ≤ (9 : Int) + d6486 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3923, d6486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31371 p hg
    simpa only [d3923, d6486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3923, d6486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3923, d6486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31373 (p : Pattern) (guard : d6326 p = 1) : d3924 p ≤ (9 : Int) + d6487 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3924, d6487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31357 p hg
    simpa only [d3924, d6487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3924, d6487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31372 p hg
    simpa only [d3924, d6487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31374 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (9 : Int) + d2 p := by
  change (10 : Int) ≤ (9 : Int) + 2
  decide
theorem compare31375 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (9 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31374 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31376 (p : Pattern) (guard : d6326 p = 1) : d3925 p ≤ (9 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d6326, d3925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31375 p hg
    simpa only [d6326, d3925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31377 (p : Pattern) (guard : d6326 p = 1) : d3926 p ≤ (9 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30939 p hg
    simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31376 p hg
    simpa only [d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31378 (p : Pattern) (guard : d6326 p = 1) : d3927 p ≤ (9 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31377 p hg
    simpa only [d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31379 (p : Pattern) (guard : d6326 p = 1) : d3928 p ≤ (9 : Int) + d6338 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3928, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31378 p hg
    simpa only [d3928, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3928, d6338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3928, d6338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31380 (p : Pattern) (guard : d6326 p = 1) : d3929 p ≤ (9 : Int) + d6355 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3929, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31030 p hg
    simpa only [d3929, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3929, d6355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31379 p hg
    simpa only [d3929, d6355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31381 (p : Pattern) (guard : d6326 p = 1) : d3930 p ≤ (9 : Int) + d6355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31380 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31067 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31382 (p : Pattern) (guard : d6326 p = 1) : d3931 p ≤ (9 : Int) + d6488 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3931, d6488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31059 p hg
    simpa only [d3931, d6488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3931, d6488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d3931, d6488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31383 (p : Pattern) (guard : d6326 p = 1) : d3932 p ≤ (9 : Int) + d6489 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3932, d6489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31381 p hg
    simpa only [d3932, d6489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3932, d6489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31382 p hg
    simpa only [d3932, d6489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31384 (p : Pattern) (guard : d6326 p = 1) : d3933 p ≤ (9 : Int) + d6490 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3933, d6490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31383 p hg
    simpa only [d3933, d6490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3933, d6490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31081 p hg
    simpa only [d3933, d6490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31385 (p : Pattern) (guard : d6326 p = 1) : d3934 p ≤ (9 : Int) + d6491 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3934, d6491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31369 p hg
    simpa only [d3934, d6491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3934, d6491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3934, d6491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31386 (p : Pattern) (guard : d6326 p = 1) : d3935 p ≤ (9 : Int) + d6492 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3935, d6492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31385 p hg
    simpa only [d3935, d6492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3935, d6492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3935, d6492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31387 (p : Pattern) (guard : d6326 p = 1) : d3936 p ≤ (9 : Int) + d6493 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3936, d6493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31386 p hg
    simpa only [d3936, d6493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3936, d6493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3936, d6493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31388 (p : Pattern) (guard : d6326 p = 1) : d3937 p ≤ (9 : Int) + d6494 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3937, d6494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31384 p hg
    simpa only [d3937, d6494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3937, d6494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31387 p hg
    simpa only [d3937, d6494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31389 (p : Pattern) (guard : d6326 p = 1) : d3938 p ≤ (9 : Int) + d6495 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3938, d6495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31373 p hg
    simpa only [d3938, d6495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3938, d6495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31388 p hg
    simpa only [d3938, d6495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31390 (p : Pattern) (guard : d6326 p = 1) : d3939 p ≤ (9 : Int) + d6496 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3939, d6496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31351 p hg
    simpa only [d3939, d6496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3939, d6496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31389 p hg
    simpa only [d3939, d6496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31391 (p : Pattern) (guard : d6326 p = 1) : d3940 p ≤ (9 : Int) + d6497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3940, d6497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31389 p hg
    simpa only [d3940, d6497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3940, d6497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3940, d6497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31392 (p : Pattern) (guard : d6326 p = 1) : d3941 p ≤ (9 : Int) + d6498 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3941, d6498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31390 p hg
    simpa only [d3941, d6498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3941, d6498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31391 p hg
    simpa only [d3941, d6498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31393 (p : Pattern) (guard : d6326 p = 1) : d3942 p ≤ (9 : Int) + d6499 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3942, d6499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31120 p hg
    simpa only [d3942, d6499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3942, d6499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31392 p hg
    simpa only [d3942, d6499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31394 (p : Pattern) (guard : d6326 p = 1) : d3943 p ≤ (9 : Int) + d6500 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3943, d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31107 p hg
    simpa only [d3943, d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3943, d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31393 p hg
    simpa only [d3943, d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31395 (p : Pattern) (guard : d6326 p = 1) : d3944 p ≤ (9 : Int) + d6501 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3944, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31165 p hg
    simpa only [d3944, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3944, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3944, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31396 (p : Pattern) (guard : d6326 p = 1) : d3945 p ≤ (9 : Int) + d6502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3945, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31242 p hg
    simpa only [d3945, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3945, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31395 p hg
    simpa only [d3945, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31397 (p : Pattern) (guard : d6326 p = 1) : d3946 p ≤ (9 : Int) + d6503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3946, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31395 p hg
    simpa only [d3946, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3946, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3946, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31398 (p : Pattern) (guard : d6326 p = 1) : d3947 p ≤ (9 : Int) + d6504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3947, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31396 p hg
    simpa only [d3947, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3947, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31397 p hg
    simpa only [d3947, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31399 (p : Pattern) (guard : d6326 p = 1) : d3948 p ≤ (9 : Int) + d6505 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3948, d6505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31225 p hg
    simpa only [d3948, d6505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3948, d6505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3948, d6505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31400 (p : Pattern) (guard : d6326 p = 1) : d3949 p ≤ (9 : Int) + d6506 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3949, d6506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31250 p hg
    simpa only [d3949, d6506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3949, d6506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31399 p hg
    simpa only [d3949, d6506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31401 (p : Pattern) (guard : d6326 p = 1) : d3950 p ≤ (9 : Int) + d6507 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3950, d6507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31399 p hg
    simpa only [d3950, d6507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3950, d6507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3950, d6507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31402 (p : Pattern) (guard : d6326 p = 1) : d3951 p ≤ (9 : Int) + d6508 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3951, d6508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31400 p hg
    simpa only [d3951, d6508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3951, d6508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31401 p hg
    simpa only [d3951, d6508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31403 (p : Pattern) (guard : d6326 p = 1) : d3952 p ≤ (9 : Int) + d6509 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3952, d6509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31398 p hg
    simpa only [d3952, d6509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3952, d6509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31402 p hg
    simpa only [d3952, d6509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31404 (p : Pattern) (guard : d6326 p = 1) : d3953 p ≤ (9 : Int) + d6510 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3953, d6510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31231 p hg
    simpa only [d3953, d6510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3953, d6510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31403 p hg
    simpa only [d3953, d6510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31405 (p : Pattern) (guard : d6326 p = 1) : d3954 p ≤ (9 : Int) + d6501 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3954, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d3954, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3954, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3954, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31406 (p : Pattern) (guard : d6326 p = 1) : d3955 p ≤ (9 : Int) + d6502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3955, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31286 p hg
    simpa only [d3955, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3955, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31405 p hg
    simpa only [d3955, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31407 (p : Pattern) (guard : d6326 p = 1) : d3956 p ≤ (9 : Int) + d6503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3956, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31405 p hg
    simpa only [d3956, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3956, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3956, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31408 (p : Pattern) (guard : d6326 p = 1) : d3957 p ≤ (9 : Int) + d6504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3957, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31406 p hg
    simpa only [d3957, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3957, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31407 p hg
    simpa only [d3957, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31409 (p : Pattern) (guard : d6326 p = 1) : d3958 p ≤ (9 : Int) + d6511 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3958, d6511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31408 p hg
    simpa only [d3958, d6511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3958, d6511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31294 p hg
    simpa only [d3958, d6511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31410 (p : Pattern) (guard : d6326 p = 1) : d3959 p ≤ (9 : Int) + d6512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3959, d6512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31285 p hg
    simpa only [d3959, d6512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3959, d6512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31409 p hg
    simpa only [d3959, d6512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31411 (p : Pattern) (guard : d6326 p = 1) : d3960 p ≤ (9 : Int) + d6513 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3960, d6513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31404 p hg
    simpa only [d3960, d6513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3960, d6513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31410 p hg
    simpa only [d3960, d6513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31412 (p : Pattern) (guard : d6326 p = 1) : d3961 p ≤ (9 : Int) + d6514 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3961, d6514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31410 p hg
    simpa only [d3961, d6514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3961, d6514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31301 p hg
    simpa only [d3961, d6514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31413 (p : Pattern) (guard : d6326 p = 1) : d3962 p ≤ (9 : Int) + d6515 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3962, d6515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31411 p hg
    simpa only [d3962, d6515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3962, d6515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31412 p hg
    simpa only [d3962, d6515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31414 (p : Pattern) (guard : d6326 p = 1) : d3963 p ≤ (9 : Int) + d1 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31267 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31415 (p : Pattern) (guard : d6326 p = 1) : d3964 p ≤ (9 : Int) + d6402 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3964, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31259 p hg
    simpa only [d3964, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3964, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3964, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31416 (p : Pattern) (guard : d6326 p = 1) : d3965 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3965, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31414 p hg
    simpa only [d3965, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3965, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31415 p hg
    simpa only [d3965, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31417 (p : Pattern) (guard : d6326 p = 1) : d3966 p ≤ (9 : Int) + d6406 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3966, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31416 p hg
    simpa only [d3966, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3966, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d3966, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31418 (p : Pattern) (guard : d6326 p = 1) : d3967 p ≤ (9 : Int) + d6407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3967, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31262 p hg
    simpa only [d3967, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3967, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31417 p hg
    simpa only [d3967, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31419 (p : Pattern) (guard : d6326 p = 1) : d3968 p ≤ (9 : Int) + d6406 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3968, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31269 p hg
    simpa only [d3968, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3968, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d3968, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31420 (p : Pattern) (guard : d6326 p = 1) : d3969 p ≤ (9 : Int) + d6409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3969, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31419 p hg
    simpa only [d3969, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3969, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31168 p hg
    simpa only [d3969, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31421 (p : Pattern) (guard : d6326 p = 1) : d3970 p ≤ (9 : Int) + d6410 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3970, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31418 p hg
    simpa only [d3970, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3970, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31420 p hg
    simpa only [d3970, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31422 (p : Pattern) (guard : d6326 p = 1) : d3971 p ≤ (9 : Int) + d6516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3971, d6516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31248 p hg
    simpa only [d3971, d6516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3971, d6516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31212 p hg
    simpa only [d3971, d6516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31423 (p : Pattern) (guard : d6326 p = 1) : d3972 p ≤ (9 : Int) + d6517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3972, d6517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31279 p hg
    simpa only [d3972, d6517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3972, d6517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31422 p hg
    simpa only [d3972, d6517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31424 (p : Pattern) (guard : d6326 p = 1) : d3973 p ≤ (9 : Int) + d6518 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3973, d6518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31423 p hg
    simpa only [d3973, d6518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3973, d6518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31399 p hg
    simpa only [d3973, d6518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31425 (p : Pattern) (guard : d6326 p = 1) : d3974 p ≤ (9 : Int) + d6519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3974, d6519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31280 p hg
    simpa only [d3974, d6519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3974, d6519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3974, d6519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31426 (p : Pattern) (guard : d6326 p = 1) : d3975 p ≤ (9 : Int) + d6520 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3975, d6520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31425 p hg
    simpa only [d3975, d6520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3975, d6520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3975, d6520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31427 (p : Pattern) (guard : d6326 p = 1) : d3976 p ≤ (9 : Int) + d6521 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3976, d6521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31426 p hg
    simpa only [d3976, d6521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3976, d6521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3976, d6521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31428 (p : Pattern) (guard : d6326 p = 1) : d3977 p ≤ (9 : Int) + d6522 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3977, d6522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31424 p hg
    simpa only [d3977, d6522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3977, d6522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31427 p hg
    simpa only [d3977, d6522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31429 (p : Pattern) (guard : d6326 p = 1) : d3978 p ≤ (9 : Int) + d6523 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3978, d6523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31421 p hg
    simpa only [d3978, d6523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3978, d6523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31428 p hg
    simpa only [d3978, d6523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31430 (p : Pattern) (guard : d6326 p = 1) : d3979 p ≤ (9 : Int) + d3 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31192 p hg
    simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31188 p hg
    simpa only [d3979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31431 (p : Pattern) (guard : d6326 p = 1) : d3980 p ≤ (9 : Int) + d3 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31189 p hg
    simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31430 p hg
    simpa only [d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31432 (p : Pattern) (guard : d6326 p = 1) : d3981 p ≤ (9 : Int) + d3 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31185 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31431 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31433 (p : Pattern) (guard : d6326 p = 1) : d3982 p ≤ (9 : Int) + d6411 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3982, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31233 p hg
    simpa only [d3982, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3982, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3982, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31434 (p : Pattern) (guard : d6326 p = 1) : d3983 p ≤ (9 : Int) + d6424 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3983, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31432 p hg
    simpa only [d3983, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3983, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31433 p hg
    simpa only [d3983, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31435 (p : Pattern) (guard : d6326 p = 1) : d3984 p ≤ (9 : Int) + d6425 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3984, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31416 p hg
    simpa only [d3984, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3984, d6425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31434 p hg
    simpa only [d3984, d6425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31436 (p : Pattern) (guard : d6326 p = 1) : d3985 p ≤ (9 : Int) + d5 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31155 p hg
    simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31218 p hg
    simpa only [d3985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31437 (p : Pattern) (guard : d6326 p = 1) : d3986 p ≤ (9 : Int) + d5 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31219 p hg
    simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31436 p hg
    simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31438 (p : Pattern) (guard : d6326 p = 1) : d3987 p ≤ (9 : Int) + d5 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31152 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31437 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31439 (p : Pattern) (guard : d6326 p = 1) : d3988 p ≤ (9 : Int) + d6404 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3988, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31157 p hg
    simpa only [d3988, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3988, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3988, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31440 (p : Pattern) (guard : d6326 p = 1) : d3989 p ≤ (9 : Int) + d6405 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3989, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31438 p hg
    simpa only [d3989, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3989, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31439 p hg
    simpa only [d3989, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31441 (p : Pattern) (guard : d6326 p = 1) : d3990 p ≤ (9 : Int) + d6501 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3990, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31440 p hg
    simpa only [d3990, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3990, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3990, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31442 (p : Pattern) (guard : d6326 p = 1) : d3991 p ≤ (9 : Int) + d6502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3991, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31435 p hg
    simpa only [d3991, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3991, d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31441 p hg
    simpa only [d3991, d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31443 (p : Pattern) (guard : d6326 p = 1) : d3992 p ≤ (9 : Int) + d6404 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3992, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31437 p hg
    simpa only [d3992, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3992, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3992, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31444 (p : Pattern) (guard : d6326 p = 1) : d3993 p ≤ (9 : Int) + d6405 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3993, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31224 p hg
    simpa only [d3993, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3993, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31443 p hg
    simpa only [d3993, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31445 (p : Pattern) (guard : d6326 p = 1) : d3994 p ≤ (9 : Int) + d6501 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3994, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31444 p hg
    simpa only [d3994, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3994, d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3994, d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31446 (p : Pattern) (guard : d6326 p = 1) : d3995 p ≤ (9 : Int) + d6503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3995, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31445 p hg
    simpa only [d3995, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3995, d6503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3995, d6503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31447 (p : Pattern) (guard : d6326 p = 1) : d3996 p ≤ (9 : Int) + d6504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3996, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31442 p hg
    simpa only [d3996, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3996, d6504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31446 p hg
    simpa only [d3996, d6504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31448 (p : Pattern) (guard : d6326 p = 1) : d3997 p ≤ (9 : Int) + d6524 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3997, d6524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31224 p hg
    simpa only [d3997, d6524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3997, d6524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31212 p hg
    simpa only [d3997, d6524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31449 (p : Pattern) (guard : d6326 p = 1) : d3998 p ≤ (9 : Int) + d6525 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3998, d6525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31448 p hg
    simpa only [d3998, d6525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3998, d6525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31225 p hg
    simpa only [d3998, d6525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31450 (p : Pattern) (guard : d6326 p = 1) : d3999 p ≤ (9 : Int) + d6526 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3999, d6526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31449 p hg
    simpa only [d3999, d6526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3999, d6526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31426 p hg
    simpa only [d3999, d6526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31451 (p : Pattern) (guard : d6326 p = 1) : d4000 p ≤ (9 : Int) + d6527 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4000, d6527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30989 p hg
    simpa only [d4000, d6527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4000, d6527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4000, d6527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31452 (p : Pattern) (guard : d6326 p = 1) : d4001 p ≤ (9 : Int) + d6528 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4001, d6528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31450 p hg
    simpa only [d4001, d6528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4001, d6528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31451 p hg
    simpa only [d4001, d6528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31453 (p : Pattern) (guard : d6326 p = 1) : d4002 p ≤ (9 : Int) + d6529 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4002, d6529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31447 p hg
    simpa only [d4002, d6529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4002, d6529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31452 p hg
    simpa only [d4002, d6529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31454 (p : Pattern) (guard : d6326 p = 1) : d4003 p ≤ (9 : Int) + d6530 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4003, d6530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31429 p hg
    simpa only [d4003, d6530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4003, d6530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31453 p hg
    simpa only [d4003, d6530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31455 (p : Pattern) (guard : d6326 p = 1) : d4004 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31269 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31272 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31456 (p : Pattern) (guard : d6326 p = 1) : d4005 p ≤ (9 : Int) + d6531 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4005, d6531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31279 p hg
    simpa only [d4005, d6531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4005, d6531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d4005, d6531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31457 (p : Pattern) (guard : d6326 p = 1) : d4006 p ≤ (9 : Int) + d6532 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4006, d6532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31455 p hg
    simpa only [d4006, d6532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4006, d6532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31456 p hg
    simpa only [d4006, d6532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31458 (p : Pattern) (guard : d6326 p = 1) : d4007 p ≤ (9 : Int) + d6533 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4007, d6533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31457 p hg
    simpa only [d4007, d6533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4007, d6533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31290 p hg
    simpa only [d4007, d6533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31459 (p : Pattern) (guard : d6326 p = 1) : d4008 p ≤ (9 : Int) + d6534 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4008, d6534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31458 p hg
    simpa only [d4008, d6534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4008, d6534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31294 p hg
    simpa only [d4008, d6534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31460 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (9 : Int) + d3 p := by
  change (11 : Int) ≤ (9 : Int) + 3
  decide
theorem compare31461 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (9 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31460 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31183 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31462 (p : Pattern) (guard : d6326 p = 1) : d326 p ≤ (9 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31181 p hg
    simpa only [d6326, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31461 p hg
    simpa only [d6326, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31463 (p : Pattern) (guard : d6326 p = 1) : d4009 p ≤ (9 : Int) + d3 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31192 p hg
    simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31462 p hg
    simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31464 (p : Pattern) (guard : d6326 p = 1) : d4010 p ≤ (9 : Int) + d3 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31189 p hg
    simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31463 p hg
    simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31465 (p : Pattern) (guard : d6326 p = 1) : d4011 p ≤ (9 : Int) + d6411 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4011, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31464 p hg
    simpa only [d4011, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4011, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4011, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31466 (p : Pattern) (guard : d6326 p = 1) : d4012 p ≤ (9 : Int) + d6424 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4012, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31248 p hg
    simpa only [d4012, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4012, d6424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31465 p hg
    simpa only [d4012, d6424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31467 (p : Pattern) (guard : d6326 p = 1) : d4013 p ≤ (9 : Int) + d6424 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31466 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31279 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31468 (p : Pattern) (guard : d6326 p = 1) : d4014 p ≤ (9 : Int) + d6535 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4014, d6535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31467 p hg
    simpa only [d4014, d6535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4014, d6535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31405 p hg
    simpa only [d4014, d6535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31469 (p : Pattern) (guard : d6326 p = 1) : d4015 p ≤ (9 : Int) + d6536 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4015, d6536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31468 p hg
    simpa only [d4015, d6536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4015, d6536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31293 p hg
    simpa only [d4015, d6536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31470 (p : Pattern) (guard : d6326 p = 1) : d4016 p ≤ (9 : Int) + d6537 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4016, d6537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31064 p hg
    simpa only [d4016, d6537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4016, d6537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4016, d6537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31471 (p : Pattern) (guard : d6326 p = 1) : d4017 p ≤ (9 : Int) + d6538 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4017, d6538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31470 p hg
    simpa only [d4017, d6538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4017, d6538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4017, d6538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31472 (p : Pattern) (guard : d6326 p = 1) : d4018 p ≤ (9 : Int) + d6539 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4018, d6539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31469 p hg
    simpa only [d4018, d6539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4018, d6539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31471 p hg
    simpa only [d4018, d6539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31473 (p : Pattern) (guard : d6326 p = 1) : d4019 p ≤ (9 : Int) + d6540 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4019, d6540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31459 p hg
    simpa only [d4019, d6540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4019, d6540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31472 p hg
    simpa only [d4019, d6540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31474 (p : Pattern) (guard : d6326 p = 1) : d4020 p ≤ (9 : Int) + d6541 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4020, d6541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31454 p hg
    simpa only [d4020, d6541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4020, d6541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31473 p hg
    simpa only [d4020, d6541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31475 (p : Pattern) (guard : d6326 p = 1) : d4021 p ≤ (9 : Int) + d6542 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4021, d6542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31279 p hg
    simpa only [d4021, d6542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4021, d6542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31063 p hg
    simpa only [d4021, d6542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31476 (p : Pattern) (guard : d6326 p = 1) : d4022 p ≤ (9 : Int) + d6543 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4022, d6543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31455 p hg
    simpa only [d4022, d6543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4022, d6543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31475 p hg
    simpa only [d4022, d6543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31477 (p : Pattern) (guard : d6326 p = 1) : d4023 p ≤ (9 : Int) + d6544 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4023, d6544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d4023, d6544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4023, d6544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31063 p hg
    simpa only [d4023, d6544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31478 (p : Pattern) (guard : d6326 p = 1) : d4024 p ≤ (9 : Int) + d6545 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4024, d6545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31477 p hg
    simpa only [d4024, d6545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4024, d6545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4024, d6545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31479 (p : Pattern) (guard : d6326 p = 1) : d4025 p ≤ (9 : Int) + d6546 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4025, d6546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31476 p hg
    simpa only [d4025, d6546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4025, d6546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31478 p hg
    simpa only [d4025, d6546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31480 (p : Pattern) (guard : d6326 p = 1) : d4026 p ≤ (9 : Int) + d6547 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4026, d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31281 p hg
    simpa only [d4026, d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4026, d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d4026, d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31481 (p : Pattern) (guard : d6326 p = 1) : d4027 p ≤ (9 : Int) + d6548 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4027, d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31480 p hg
    simpa only [d4027, d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4027, d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4027, d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31482 (p : Pattern) (guard : d6326 p = 1) : d4028 p ≤ (9 : Int) + d6549 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4028, d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31481 p hg
    simpa only [d4028, d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4028, d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4028, d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31483 (p : Pattern) (guard : d6326 p = 1) : d4029 p ≤ (9 : Int) + d6550 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4029, d6550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31479 p hg
    simpa only [d4029, d6550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4029, d6550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31482 p hg
    simpa only [d4029, d6550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31484 (p : Pattern) (guard : d6326 p = 1) : d4030 p ≤ (9 : Int) + d6551 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4030, d6551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31483 p hg
    simpa only [d4030, d6551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4030, d6551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31472 p hg
    simpa only [d4030, d6551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31485 (p : Pattern) (guard : d6326 p = 1) : d4031 p ≤ (9 : Int) + d6552 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4031, d6552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31484 p hg
    simpa only [d4031, d6552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4031, d6552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d4031, d6552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31486 (p : Pattern) (guard : d6326 p = 1) : d4032 p ≤ (9 : Int) + d6553 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4032, d6553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31474 p hg
    simpa only [d4032, d6553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4032, d6553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31485 p hg
    simpa only [d4032, d6553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31487 (p : Pattern) (guard : d6326 p = 1) : d4033 p ≤ (9 : Int) + d6554 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4033, d6554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31413 p hg
    simpa only [d4033, d6554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4033, d6554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31486 p hg
    simpa only [d4033, d6554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31488 (p : Pattern) (guard : d6326 p = 1) : d4034 p ≤ (9 : Int) + d6555 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4034, d6555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31107 p hg
    simpa only [d4034, d6555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4034, d6555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31487 p hg
    simpa only [d4034, d6555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31489 (p : Pattern) (guard : d6326 p = 1) : d4035 p ≤ (9 : Int) + d6556 p := by
  cases selected : p 49 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4035, d6556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31394 p hg
    simpa only [d4035, d6556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4035, d6556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31488 p hg
    simpa only [d4035, d6556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31490 (p : Pattern) (guard : d6326 p = 1) : d4036 p ≤ (9 : Int) + d6557 p := by
  cases selected : p 48 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d4036, d6557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31313 p hg
    simpa only [d4036, d6557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d4036, d6557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31489 p hg
    simpa only [d4036, d6557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31491 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14530 p hg
    simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31492 (p : Pattern) (guard : d5848 p = 1) : d3541 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29206 p hg
    simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31491 p hg
    simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31493 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d318 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31494 (p : Pattern) (guard : d5849 p = 1) : d3542 p ≤ (0 : Int) + d2184 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3542, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31492 p hg
    simpa only [d5849, d3542, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3542, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31493 p hg
    simpa only [d5849, d3542, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31495 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31496 (p : Pattern) (guard : d5847 p = 1) : d3543 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3543, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3543, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3543, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31495 p hg
    simpa only [d5847, d3543, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31497 (p : Pattern) (guard : d5848 p = 1) : d3544 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31496 p hg
    simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31498 (p : Pattern) (guard : d5849 p = 1) : d3545 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3545, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31497 p hg
    simpa only [d5849, d3545, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3545, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29212 p hg
    simpa only [d5849, d3545, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31499 (p : Pattern) (guard : d5849 p = 1) : d3546 p ≤ (0 : Int) + d2186 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3546, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31494 p hg
    simpa only [d3546, d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3546, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d3546, d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
